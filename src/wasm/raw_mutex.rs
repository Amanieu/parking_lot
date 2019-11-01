// Eventually, when access to WASM i32_atomic_wait is stable, this should look more like
// https://github.com/rust-lang/rust/blob/f51752774bbbe48d2aabe53c86e9e91ed3a73a5d/src/libstd/sys/wasm/mutex_atomics.rs#L81-L160
//
// For now, we essentially do what
// https://github.com/rust-lang/rust/blob/253fc0ed742c235fa34c5d78814fa7b8a5e5e055/src/libstd/sys/wasm/mutex.rs does.

use std::cell::UnsafeCell;

const LOCKED_BIT: u8 = 1;
const PARKED_BIT: u8 = 2;

// UnparkToken used to indicate that that the target thread should attempt to
// lock the mutex again as soon as it is unparked.
pub(crate) const TOKEN_NORMAL: UnparkToken = UnparkToken(0);

// UnparkToken used to indicate that the mutex is being handed off to the target
// thread directly without unlocking it.
pub(crate) const TOKEN_HANDOFF: UnparkToken = UnparkToken(1);

/// Raw mutex type backed by the parking lot.
pub struct RawMutex {
    state: UnsafeCell<u8>,
}

unsafe impl Send for RawMutex {}
unsafe impl Sync for RawMutex {} // no threads on wasm

use crate::deadlock;
use core::time::Duration;
use lock_api::{GuardSend, RawMutex as RawMutexTrait, RawMutexFair, RawMutexTimed};
use parking_lot_core::{self, UnparkToken};
use std::time::Instant;

unsafe impl RawMutexTrait for RawMutex {
    const INIT: RawMutex = RawMutex {
        state: UnsafeCell::new(0u8),
    };

    type GuardMarker = GuardSend;

    #[inline]
    fn lock(&self) {
        unsafe {
            let state = self.state.get();
            assert!(
                (*state & LOCKED_BIT) == 0,
                "cannot recursively acquire Mutex"
            );
            *state = *state | LOCKED_BIT;
            deadlock::acquire_resource(self as *const _ as usize);
        };
    }

    #[inline]
    fn try_lock(&self) -> bool {
        let state = self.state.get();
        unsafe {
            if *state & LOCKED_BIT > 0 {
                false
            } else {
                *state |= *state;
                deadlock::acquire_resource(self as *const _ as usize);
                true
            }
        }
    }

    #[inline]
    fn unlock(&self) {
        unsafe {
            deadlock::release_resource(self as *const _ as usize);
            let state = self.state.get();
            *state &= !LOCKED_BIT;
        };
    }
}

unsafe impl RawMutexTimed for RawMutex {
    type Duration = Duration;
    type Instant = Instant;

    #[inline]
    fn try_lock_until(&self, _timeout: Instant) -> bool {
        self.try_lock()
    }

    #[inline]
    fn try_lock_for(&self, _timeout: Duration) -> bool {
        self.try_lock()
    }
}

unsafe impl RawMutexFair for RawMutex {
    #[inline]
    fn unlock_fair(&self) {
        self.unlock()
    }

    #[inline]
    fn bump(&self) {}
}

impl RawMutex {
    // Used by Condvar when requeuing threads to us, must be called while
    // holding the queue lock.
    // false if unlocked
    #[inline]
    pub(crate) fn mark_parked_if_locked(&self) -> bool {
        unsafe {
            let state = self.state.get();
            if *state & LOCKED_BIT > 0 {
                false
            } else {
                *state &= PARKED_BIT;
                true
            }
        }
    }

    // Used by Condvar when requeuing threads to us, must be called while
    // holding the queue lock.
    #[inline]
    pub(crate) fn mark_parked(&self) {
        unsafe {
            *self.state.get() &= !PARKED_BIT;
        }
    }
}
