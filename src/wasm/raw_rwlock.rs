// Copyright 2019 Cormac Relf
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use core::cell::UnsafeCell;
use core::time::Duration;
use lock_api::{
    GuardSend, RawRwLock as RawRwLockTrait, RawRwLockDowngrade, RawRwLockFair, RawRwLockRecursive,
    RawRwLockRecursiveTimed, RawRwLockTimed, RawRwLockUpgrade, RawRwLockUpgradeDowngrade,
    RawRwLockUpgradeFair, RawRwLockUpgradeTimed,
};
use parking_lot_core::deadlock;
use std::time::Instant;

// This reader-writer lock implementation is based on Boost's upgrade_mutex:
// https://github.com/boostorg/thread/blob/fc08c1fe2840baeeee143440fba31ef9e9a813c8/include/boost/thread/v2/shared_mutex.hpp#L432
//
// This implementation uses 2 wait queues, one at key [addr] and one at key
// [addr + 1]. The primary queue is used for all new waiting threads, and the
// secondary queue is used by the thread which has acquired WRITER_BIT but is
// waiting for the remaining readers to exit the lock.
//
// This implementation is fair between readers and writers since it uses the
// order in which threads first started queuing to alternate between read phases
// and write phases. In particular is it not vulnerable to write starvation
// since readers will block if there is a pending writer.

// There is at least one thread in the main queue.
const PARKED_BIT: usize = 0b0001;
// There is a parked thread holding WRITER_BIT. WRITER_BIT must be set.
const WRITER_PARKED_BIT: usize = 0b0010;
// A reader is holding an upgradable lock. The reader count must be non-zero and
// WRITER_BIT must not be set.
const UPGRADABLE_BIT: usize = 0b0100;
// If the reader count is zero: a writer is currently holding an exclusive lock.
// Otherwise: a writer is waiting for the remaining readers to exit the lock.
const WRITER_BIT: usize = 0b1000;
// Mask of bits used to count readers.
const READERS_MASK: usize = !0b1111;
// Base unit for counting readers.
const ONE_READER: usize = 0b10000;

// Token indicating what type of lock a queued thread is trying to acquire
// const TOKEN_SHARED: ParkToken = ParkToken(ONE_READER);
// const TOKEN_EXCLUSIVE: ParkToken = ParkToken(WRITER_BIT);
// const TOKEN_UPGRADABLE: ParkToken = ParkToken(ONE_READER | UPGRADABLE_BIT);

/// Raw reader-writer lock type backed by the parking lot.
pub struct RawRwLock {
    state: UnsafeCell<usize>,
}

unsafe impl Send for RawRwLock {}
unsafe impl Sync for RawRwLock {} // no threads on wasm

unsafe impl RawRwLockTrait for RawRwLock {
    const INIT: RawRwLock = RawRwLock {
        state: UnsafeCell::new(0),
    };

    type GuardMarker = GuardSend;

    #[inline]
    fn lock_exclusive(&self) {
        let res = self.try_lock_exclusive();
        if !res {
            panic!("could not acquire exclusive lock");
        }
    }

    #[inline]
    fn try_lock_exclusive(&self) -> bool {
        unsafe {
            let state = self.state.get();
            if *state == 0 {
                *state = WRITER_BIT;
                self.deadlock_acquire();
                true
            } else {
                false
            }
        }
    }

    #[inline]
    fn unlock_exclusive(&self) {
        self.deadlock_release();
        unsafe {
            let state = self.state.get();
            if *state == WRITER_BIT {
                *state = 0;
            } else {
                panic!("did not have exclusive lock to unlock")
            }
        }
    }

    #[inline]
    fn lock_shared(&self) {
        self.try_lock_shared_fast(false);
        self.deadlock_acquire();
    }

    #[inline]
    fn try_lock_shared(&self) -> bool {
        self.lock_shared();
        true
    }

    #[inline]
    fn unlock_shared(&self) {
        self.deadlock_release();
        let state = self.state.get();
        unsafe {
            *state = (*state)
                .checked_sub(ONE_READER)
                .expect("RwLock reader count underflow");
            if *state & (READERS_MASK | WRITER_PARKED_BIT) == (ONE_READER | WRITER_PARKED_BIT) {
                panic!("impossible?")
            }
        }
    }
}

unsafe impl RawRwLockFair for RawRwLock {
    #[inline]
    fn unlock_shared_fair(&self) {
        // Shared unlocking is always fair in this implementation.
        self.unlock_shared();
    }

    #[inline]
    fn unlock_exclusive_fair(&self) {
        self.unlock_exclusive();
    }

    #[inline]
    fn bump_shared(&self) {}

    #[inline]
    fn bump_exclusive(&self) {}
}

unsafe impl RawRwLockDowngrade for RawRwLock {
    #[inline]
    fn downgrade(&self) {
        let state = self.state.get();
        unsafe {
            *state = *state + (ONE_READER - WRITER_BIT);
            // Wake up parked shared and upgradable threads if there are any
            if *state & PARKED_BIT != 0 {
                // self.downgrade_slow();
            }
        }
    }
}

unsafe impl RawRwLockTimed for RawRwLock {
    type Duration = Duration;
    type Instant = Instant;

    #[inline]
    fn try_lock_shared_for(&self, _timeout: Self::Duration) -> bool {
        self.try_lock_shared()
    }

    #[inline]
    fn try_lock_shared_until(&self, _timeout: Self::Instant) -> bool {
        self.try_lock_shared()
    }

    #[inline]
    fn try_lock_exclusive_for(&self, _timeout: Duration) -> bool {
        self.try_lock_exclusive()
    }

    #[inline]
    fn try_lock_exclusive_until(&self, _timeout: Instant) -> bool {
        self.try_lock_exclusive()
    }
}

unsafe impl RawRwLockRecursive for RawRwLock {
    #[inline]
    fn lock_shared_recursive(&self) {
        let result = self.try_lock_shared_fast(true);
        if !result {
            panic!("could not acquire shared recursive lock");
        }
        self.deadlock_acquire();
    }

    #[inline]
    fn try_lock_shared_recursive(&self) -> bool {
        let result = self.try_lock_shared_fast(true);
        if result {
            self.deadlock_acquire();
        }
        result
    }
}

unsafe impl RawRwLockRecursiveTimed for RawRwLock {
    #[inline]
    fn try_lock_shared_recursive_for(&self, _timeout: Self::Duration) -> bool {
        self.try_lock_shared_recursive()
    }

    #[inline]
    fn try_lock_shared_recursive_until(&self, _timeout: Self::Instant) -> bool {
        self.try_lock_shared_recursive()
    }
}

unsafe impl RawRwLockUpgrade for RawRwLock {
    #[inline]
    fn lock_upgradable(&self) {
        if !self.try_lock_upgradable_fast() {
            panic!("could not lock upgradble");
        }
    }

    #[inline]
    fn try_lock_upgradable(&self) -> bool {
        let res = self.try_lock_upgradable_fast();
        if res {
            self.deadlock_acquire();
        }
        res
    }

    #[inline]
    fn unlock_upgradable(&self) {
        self.deadlock_release();
        let state = self.state.get();
        unsafe {
            if *state & PARKED_BIT == 0 {
                *state -= ONE_READER | UPGRADABLE_BIT;
            }
        }
    }

    #[inline]
    fn upgrade(&self) {
        let state = self.state.get();
        unsafe {
            *state -= (ONE_READER | UPGRADABLE_BIT) - WRITER_BIT;
            if *state & READERS_MASK != ONE_READER {
                panic!("cannot upgrade")
            }
        }
    }

    #[inline]
    fn try_upgrade(&self) -> bool {
        let state = self.state.get();
        unsafe {
            if *state == ONE_READER | UPGRADABLE_BIT {
                *state = WRITER_BIT;
                true
            } else {
                false
            }
        }
    }
}

unsafe impl RawRwLockUpgradeFair for RawRwLock {
    #[inline]
    fn unlock_upgradable_fair(&self) {
        self.unlock_upgradable();
    }

    #[inline]
    fn bump_upgradable(&self) {}
}

unsafe impl RawRwLockUpgradeDowngrade for RawRwLock {
    #[inline]
    fn downgrade_upgradable(&self) {
        let state = self.state.get();
        unsafe {
            *state -= UPGRADABLE_BIT;
            // Wake up parked upgradable threads if there are any
            if *state & PARKED_BIT != 0 {
                panic!("cannot downgrade_slow on wasm, as no parking");
                // self.downgrade_slow();
            }
        }
    }

    #[inline]
    fn downgrade_to_upgradable(&self) {
        let state = self.state.get();
        unsafe {
            *state += (ONE_READER | UPGRADABLE_BIT) - WRITER_BIT;

            // Wake up parked shared threads if there are any
            if *state & PARKED_BIT != 0 {
                panic!("cannot downgrade_to_upgradable_slow on wasm, as no parking");
            }
        }
    }
}

unsafe impl RawRwLockUpgradeTimed for RawRwLock {
    #[inline]
    fn try_lock_upgradable_until(&self, _timeout: Instant) -> bool {
        self.try_lock_upgradable()
    }

    #[inline]
    fn try_lock_upgradable_for(&self, _timeout: Duration) -> bool {
        self.try_lock_upgradable()
    }

    #[inline]
    fn try_upgrade_until(&self, _timeout: Self::Instant) -> bool {
        let state = self.state.get();
        unsafe {
            *state = (*state) - (ONE_READER | UPGRADABLE_BIT) - WRITER_BIT;
            *state & READERS_MASK == ONE_READER
        }
    }

    #[inline]
    fn try_upgrade_for(&self, _timeout: Duration) -> bool {
        let state = self.state.get();
        unsafe {
            *state = (*state) - (ONE_READER | UPGRADABLE_BIT) - WRITER_BIT;
            *state & READERS_MASK == ONE_READER
        }
    }
}

impl RawRwLock {
    #[inline(always)]
    fn try_lock_shared_fast(&self, recursive: bool) -> bool {
        let state = self.state.get();

        unsafe {
            // We can't allow grabbing a shared lock if there is a writer, even if
            // the writer is still waiting for the remaining readers to exit.
            if *state & WRITER_BIT != 0 {
                // To allow recursive locks, we make an exception and allow readers
                // to skip ahead of a pending writer to avoid deadlocking, at the
                // cost of breaking the fairness guarantees.
                if !recursive || *state & READERS_MASK == 0 {
                    return false;
                }
            }
            *state = (*state)
                .checked_add(ONE_READER)
                .expect("RwLock reader count overflow");
        }
        true
    }

    #[inline(always)]
    fn try_lock_upgradable_fast(&self) -> bool {
        let state = self.state.get();

        unsafe {
            // We can't grab an upgradable lock if there is already a writer or
            // upgradable reader.
            if *state & (WRITER_BIT | UPGRADABLE_BIT) != 0 {
                return false;
            }

            if let Some(new_state) = (*state).checked_add(ONE_READER | UPGRADABLE_BIT) {
                *state = new_state;
                true
            } else {
                false
            }
        }
    }

    #[inline]
    fn deadlock_acquire(&self) {
        unsafe { deadlock::acquire_resource(self as *const _ as usize) };
        unsafe { deadlock::acquire_resource(self as *const _ as usize + 1) };
    }

    #[inline]
    fn deadlock_release(&self) {
        unsafe { deadlock::release_resource(self as *const _ as usize) };
        unsafe { deadlock::release_resource(self as *const _ as usize + 1) };
    }
}
