// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::elision::{have_elision, AtomicElisionExt};
use core::sync::atomic::{AtomicUsize, Ordering};
use parking_lot_core::{self, deadlock, SpinWait};
use std::thread;
use std::time::Duration;

// If the reader count is zero: a writer is currently holding an exclusive lock.
// Otherwise: a writer is waiting for the remaining readers to exit the lock.
const WRITER_BIT: usize = 0b1000;
// Mask of bits used to count readers.
const READERS_MASK: usize = !0b1111;
// Base unit for counting readers.
const ONE_READER: usize = 0b10000;

/// A reader-writer lock
///
/// This type of lock allows a number of readers or at most one writer at any
/// point in time. The write portion of this lock typically allows modification
/// of the underlying data (exclusive access) and the read portion of this lock
/// typically allows for read-only access (shared access).
///
/// This lock uses a task-fair locking policy which avoids both reader and
/// writer starvation. This means that readers trying to acquire the lock will
/// block even if the lock is unlocked when there are writers waiting to acquire
/// the lock. Because of this, attempts to recursively acquire a read lock
/// within a single thread may result in a deadlock.
///
/// The type parameter `T` represents the data that this lock protects. It is
/// required that `T` satisfies `Send` to be shared across threads and `Sync` to
/// allow concurrent access through readers. The RAII guards returned from the
/// locking methods implement `Deref` (and `DerefMut` for the `write` methods)
/// to allow access to the contained of the lock.
///
/// # Fairness
///
/// A typical unfair lock can often end up in a situation where a single thread
/// quickly acquires and releases the same lock in succession, which can starve
/// other threads waiting to acquire the rwlock. While this improves throughput
/// because it doesn't force a context switch when a thread tries to re-acquire
/// a rwlock it has just released, this can starve other threads.
///
/// This rwlock uses [eventual fairness](https://trac.webkit.org/changeset/203350)
/// to ensure that the lock will be fair on average without sacrificing
/// throughput. This is done by forcing a fair unlock on average every 0.5ms,
/// which will force the lock to go to the next thread waiting for the rwlock.
///
/// Additionally, any critical section longer than 1ms will always use a fair
/// unlock, which has a negligible impact on throughput considering the length
/// of the critical section.
///
/// You can also force a fair unlock by calling `RwLockReadGuard::unlock_fair`
/// or `RwLockWriteGuard::unlock_fair` when unlocking a mutex instead of simply
/// dropping the guard.
///
/// # Differences from the standard library `SegRwLock`
///
/// - Supports atomically downgrading a write lock into a read lock.
/// - Task-fair locking policy instead of an unspecified platform default.
/// - No poisoning, the lock is released normally on panic.
/// - Only requires 1 word of space, whereas the standard library boxes the
///   `SegRwLock` due to platform limitations.
/// - Can be statically constructed.
/// - Does not require any drop glue when dropped.
/// - Inline fast path for the uncontended case.
/// - Efficient handling of micro-contention using adaptive spinning.
/// - Allows raw locking & unlocking without a guard.
/// - Supports eventual fairness so that the rwlock is fair on average.
/// - Optionally allows making the rwlock fair by calling
///   `RwLockReadGuard::unlock_fair` and `RwLockWriteGuard::unlock_fair`.
///
/// # Examples
///
/// ```
/// use parking_lot::SegRwLock;
///
/// let lock = SegRwLock::new(5);
///
/// // many reader locks can be held at once
/// {
///     let r1 = lock.read();
///     let r2 = lock.read();
///     assert_eq!(*r1, 5);
///     assert_eq!(*r2, 5);
/// } // read locks are dropped at this point
///
/// // only one write lock may be held, however
/// {
///     let mut w = lock.write();
///     *w += 1;
///     assert_eq!(*w, 6);
/// } // write lock is dropped here
/// ```
pub type SegRwLock<T> = lock_api::RwLock<SegRawRwLock, T>;

/// Creates a new instance of an `SegRwLock<T>` which is unlocked.
///
/// This allows creating a `SegRwLock<T>` in a constant context on stable Rust.
pub const fn const_seg_rwlock<T>(val: T) -> SegRwLock<T> {
    SegRwLock::const_new(<SegRawRwLock as lock_api::RawRwLock>::INIT, val)
}

/// RAII structure used to release the shared read access of a lock when
/// dropped.
pub type SegRwLockReadGuard<'a, T> = lock_api::RwLockReadGuard<'a, SegRawRwLock, T>;

/// RAII structure used to release the exclusive write access of a lock when
/// dropped.
pub type SegRwLockWriteGuard<'a, T> = lock_api::RwLockWriteGuard<'a, SegRawRwLock, T>;

/// Segment Raw reader-writer lock type backed by the parking lot.
pub struct SegRawRwLock {
    read_state: AtomicUsize,
    #[cfg(any(
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "powerpc64",
    ))]
    _cache_padded: [u8; 120usize], //128 bytes cacheline align
    #[cfg(any(
        target_arch = "arm",
        target_arch = "mips",
        target_arch = "mips64",
        target_arch = "riscv32",
        target_arch = "riscv64",
        target_arch = "sparc",
        target_arch = "hexagon",
    ))]
    _cache_padded: [u8; 28usize], //32 bytes cacheline align
    #[cfg(not(any(
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "powerpc64",
        target_arch = "arm",
        target_arch = "mips",
        target_arch = "mips64",
        target_arch = "riscv32",
        target_arch = "riscv64",
        target_arch = "sparc",
        target_arch = "hexagon",
    )))]
    _cache_padded: [u8; 56usize], //64 bytes cacheline align
    write_state: AtomicUsize,
}

unsafe impl lock_api::RawRwLock for SegRawRwLock {
    const INIT: SegRawRwLock = SegRawRwLock {
        read_state: AtomicUsize::new(0),
        #[cfg(any(
            target_arch = "x86_64",
            target_arch = "aarch64",
            target_arch = "powerpc64",
        ))]
        _cache_padded: [0; 120],
        #[cfg(any(
            target_arch = "arm",
            target_arch = "mips",
            target_arch = "mips64",
            target_arch = "riscv32",
            target_arch = "riscv64",
            target_arch = "sparc",
            target_arch = "hexagon",
        ))]
        _cache_padded: [0; 28],
        #[cfg(not(any(
            target_arch = "x86_64",
            target_arch = "aarch64",
            target_arch = "powerpc64",
            target_arch = "arm",
            target_arch = "mips",
            target_arch = "mips64",
            target_arch = "riscv32",
            target_arch = "riscv64",
            target_arch = "sparc",
            target_arch = "hexagon",
        )))]
        _cache_padded: [0; 56],
        write_state: AtomicUsize::new(0),
    };

    type GuardMarker = crate::GuardMarker;

    #[inline]
    fn lock_exclusive(&self) {
        if self
            .write_state
            .compare_exchange_weak(0, WRITER_BIT, Ordering::Acquire, Ordering::Relaxed)
            .is_err()
        {
            let result = self.lock_exclusive_slow();
            debug_assert!(result);
        }
        self.deadlock_acquire();
    }

    #[inline]
    fn try_lock_exclusive(&self) -> bool {
        if self
            .write_state
            .compare_exchange(0, WRITER_BIT, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()
        {
            self.deadlock_acquire();
            true
        } else {
            false
        }
    }

    #[inline]
    unsafe fn unlock_exclusive(&self) {
        self.deadlock_release();
        if self
            .write_state
            .compare_exchange(WRITER_BIT, 0, Ordering::Release, Ordering::Relaxed)
            .is_ok()
        {
            return;
        }
        self.unlock_exclusive_slow();
    }

    #[inline]
    fn lock_shared(&self) {
        if !self.try_lock_shared_fast(false) {
            let result = self.lock_shared_slow(false);
            debug_assert!(result);
        }
        self.deadlock_acquire();
    }

    #[inline]
    fn try_lock_shared(&self) -> bool {
        let result = if self.try_lock_shared_fast(false) {
            true
        } else {
            self.try_lock_shared_slow(false)
        };
        if result {
            self.deadlock_acquire();
        }
        result
    }

    #[inline]
    unsafe fn unlock_shared(&self) {
        self.deadlock_release();
        if have_elision() {
            self.read_state.elision_fetch_sub_release(ONE_READER)
        } else {
            self.read_state.fetch_sub(ONE_READER, Ordering::Release)
        };
    }

    #[inline]
    fn is_locked(&self) -> bool {
        let read_state = self.read_state.load(Ordering::Relaxed);
        let write_state = self.write_state.load(Ordering::Relaxed);
        (read_state & READERS_MASK) | (write_state & WRITER_BIT) != 0
    }

    #[inline]
    fn is_locked_exclusive(&self) -> bool {
        let state = self.write_state.load(Ordering::Relaxed);
        state & (WRITER_BIT) != 0
    }
}

impl SegRawRwLock {
    #[inline(always)]
    fn try_lock_shared_fast(&self, recursive: bool) -> bool {
        let write_state = self.write_state.load(Ordering::Relaxed);
        let read_state = self.read_state.load(Ordering::Relaxed);

        // We can't allow grabbing a shared lock if there is a writer, even if
        // the writer is still waiting for the remaining readers to exit.
        if write_state & WRITER_BIT != 0 {
            // To allow recursive locks, we make an exception and allow readers
            // to skip ahead of a pending writer to avoid deadlocking, at the
            // cost of breaking the fairness guarantees.
            if !recursive {
                return false;
            }
        }

        // Use hardware lock elision to avoid cache conflicts when multiple
        // readers try to acquire the lock. We only do this if the lock is
        // completely empty since elision handles conflicts poorly.
        if have_elision() && read_state == 0 {
            self.read_state
                .elision_compare_exchange_acquire(0, ONE_READER)
                .is_ok()
        } else if let Some(new_state) = read_state.checked_add(ONE_READER) {
            self.read_state
                .compare_exchange_weak(read_state, new_state, Ordering::Acquire, Ordering::Relaxed)
                .is_ok()
        } else {
            false
        }
    }

    #[cold]
    fn try_lock_shared_slow(&self, recursive: bool) -> bool {
        let mut read_state = self.read_state.load(Ordering::Relaxed);
        loop {
            let write_state = self.write_state.load(Ordering::Relaxed);
            // This mirrors the condition in try_lock_shared_fast
            if write_state & WRITER_BIT != 0 {
                if !recursive || read_state & READERS_MASK == 0 {
                    return false;
                }
            }

            if have_elision() && read_state == 0 {
                match self
                    .read_state
                    .elision_compare_exchange_acquire(0, ONE_READER)
                {
                    Ok(_) => return true,
                    Err(x) => read_state = x,
                }
            } else {
                match self.read_state.compare_exchange_weak(
                    read_state,
                    read_state
                        .checked_add(ONE_READER)
                        .expect("RwLock reader count overflow"),
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return true,
                    Err(x) => read_state = x,
                }
            }
        }
    }

    #[cold]
    fn lock_exclusive_slow(&self) -> bool {
        let try_lock = |write_state: &mut usize| {
            loop {
                if *write_state & WRITER_BIT != 0 {
                    return false;
                }

                // Grab WRITER_BIT if it isn't set, even if there are parked threads.
                match self.write_state.compare_exchange_weak(
                    *write_state,
                    *write_state | WRITER_BIT,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return true,
                    Err(x) => *write_state = x,
                }
            }
        };

        // Step 1: grab exclusive ownership of WRITER_BIT
        let timed_out = !self.lock_common(try_lock);
        if timed_out {
            return false;
        }

        // Step 2: wait for all remaining readers to exit the lock.
        self.wait_for_readers()
    }

    #[cold]
    fn unlock_exclusive_slow(&self) {
        // Should not be here for write unlock
        self.write_state
            .compare_exchange(WRITER_BIT, 0, Ordering::Release, Ordering::Relaxed)
            .expect("Exclusive unlock SegRwLock failure!");
    }

    #[cold]
    fn lock_shared_slow(&self, recursive: bool) -> bool {
        let try_lock = |write_state: &mut usize| {
            let mut spinwait_shared = SpinWait::new();
            let mut read_state = self.read_state.load(Ordering::Relaxed);
            loop {
                // Use hardware lock elision to avoid cache conflicts when multiple
                // readers try to acquire the lock. We only do this if the lock is
                // completely empty since elision handles conflicts poorly.
                if have_elision() && read_state == 0 {
                    match self
                        .read_state
                        .elision_compare_exchange_acquire(0, ONE_READER)
                    {
                        Ok(_) => return true,
                        Err(x) => read_state = x,
                    }
                }

                // This is the same condition as try_lock_shared_fast
                if *write_state & WRITER_BIT != 0 {
                    if !recursive || read_state & READERS_MASK == 0 {
                        return false;
                    }
                }

                if self
                    .read_state
                    .compare_exchange_weak(
                        read_state,
                        read_state
                            .checked_add(ONE_READER)
                            .expect("RwLock reader count overflow"),
                        Ordering::Acquire,
                        Ordering::Relaxed,
                    )
                    .is_ok()
                {
                    return true;
                }

                // If there is high contention on the reader count then we want
                // to leave some time between attempts to acquire the lock to
                // let other threads make progress.
                spinwait_shared.spin_no_yield();
                read_state = self.read_state.load(Ordering::Relaxed);
                *write_state = self.write_state.load(Ordering::Relaxed);
            }
        };
        self.lock_common(try_lock)
    }

    // Common code for waiting for readers to exit the lock after acquiring
    // WRITER_BIT.
    #[inline]
    fn wait_for_readers(&self) -> bool {
        // At this point WRITER_BIT is already set, we just need to wait for the
        // remaining readers to exit the lock.
        let mut spinwait = SpinWait::new();
        let mut read_state = self.read_state.load(Ordering::Acquire);
        while read_state & READERS_MASK != 0 {
            // Spin a few times to wait for readers to exit
            if spinwait.spin() {
                read_state = self.read_state.load(Ordering::Acquire);
                continue;
            }

            // Sleep 1ms before reset spinwait
            thread::sleep(Duration::from_millis(1));
            spinwait.reset();
            read_state = self.read_state.load(Ordering::Acquire);
        }
        true
    }

    /// Common code for acquiring a lock
    #[inline]
    fn lock_common(&self, mut try_lock: impl FnMut(&mut usize) -> bool) -> bool {
        let mut spinwait = SpinWait::new();
        let mut write_state = self.write_state.load(Ordering::Relaxed);
        loop {
            // Attempt to grab the lock
            if try_lock(&mut write_state) {
                return true;
            }

            // If there are no parked threads, try spinning a few times.
            if spinwait.spin() {
                write_state = self.write_state.load(Ordering::Relaxed);
                continue;
            }

            // Loop back and try locking again
            thread::sleep(Duration::from_millis(1));
            spinwait.reset();
            write_state = self.write_state.load(Ordering::Relaxed);
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
