// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use cloudabi as abi;
use core::{
    cell::Cell,
    mem,
    sync::atomic::{AtomicU32, Ordering},
};
use std::{convert::TryFrom, thread, time::Instant};

extern "C" {
    #[thread_local]
    static __pthread_thread_id: abi::tid;
}

struct Lock {
    lock: AtomicU32,
}

impl Lock {
    #[inline]
    pub fn new() -> Self {
        Lock {
            lock: AtomicU32::new(abi::LOCK_UNLOCKED.0),
        }
    }

    #[inline]
    unsafe fn try_lock(&self) -> bool {
        // Attempt to acquire the lock.
        if let Err(old) = self.lock.compare_exchange(
            abi::LOCK_UNLOCKED.0,
            __pthread_thread_id.0 | abi::LOCK_WRLOCKED.0,
            Ordering::Acquire,
            Ordering::Relaxed,
        ) {
            // Failure. Crash upon recursive acquisition.
            debug_assert_ne!(
                old & !abi::LOCK_KERNEL_MANAGED.0,
                __pthread_thread_id.0 | abi::LOCK_WRLOCKED.0,
                "Attempted to recursive write-lock a lock",
            );
            false
        } else {
            true
        }
    }

    #[inline]
    pub unsafe fn lock(&self) {
        if !self.try_lock() {
            // Call into the kernel to acquire a write lock.
            let subscription = abi::subscription {
                type_: abi::eventtype::LOCK_WRLOCK,
                union: abi::subscription_union {
                    lock: abi::subscription_lock {
                        lock: self.ptr(),
                        lock_scope: abi::scope::PRIVATE,
                    },
                },
                ..mem::zeroed()
            };
            let mut event: abi::event = mem::uninitialized();
            let mut nevents: usize = mem::uninitialized();
            let ret = abi::poll(&subscription, &mut event, 1, &mut nevents);
            debug_assert_eq!(ret, abi::errno::SUCCESS);
            debug_assert_eq!(event.error, abi::errno::SUCCESS);
        }
    }

    #[inline]
    pub unsafe fn unlock(&self) {
        debug_assert_eq!(
            self.lock.load(Ordering::Relaxed) & !abi::LOCK_KERNEL_MANAGED.0,
            __pthread_thread_id.0 | abi::LOCK_WRLOCKED.0,
            "This lock is not write-locked by this thread"
        );

        if !self
            .lock
            .compare_exchange(
                __pthread_thread_id.0 | abi::LOCK_WRLOCKED.0,
                abi::LOCK_UNLOCKED.0,
                Ordering::Release,
                Ordering::Relaxed,
            )
            .is_ok()
        {
            // Lock is managed by kernelspace. Call into the kernel
            // to unblock waiting threads.
            let ret = abi::lock_unlock(self.ptr(), abi::scope::PRIVATE);
            debug_assert_eq!(ret, abi::errno::SUCCESS);
        }
    }

    #[inline]
    fn ptr(&self) -> *mut abi::lock {
        &self.lock as *const AtomicU32 as *mut abi::lock
    }
}

struct Condvar {
    condvar: AtomicU32,
}

impl Condvar {
    #[inline]
    pub fn new() -> Self {
        Condvar {
            condvar: AtomicU32::new(abi::CONDVAR_HAS_NO_WAITERS.0),
        }
    }

    #[inline]
    pub unsafe fn wait(&self, lock: &Lock) {
        let subscription = abi::subscription {
            type_: abi::eventtype::CONDVAR,
            union: abi::subscription_union {
                condvar: abi::subscription_condvar {
                    condvar: self.ptr(),
                    condvar_scope: abi::scope::PRIVATE,
                    lock: lock.ptr(),
                    lock_scope: abi::scope::PRIVATE,
                },
            },
            ..mem::zeroed()
        };
        let mut event: abi::event = mem::uninitialized();
        let mut nevents: usize = mem::uninitialized();

        let ret = abi::poll(&subscription, &mut event, 1, &mut nevents);
        debug_assert_eq!(ret, abi::errno::SUCCESS);
        debug_assert_eq!(event.error, abi::errno::SUCCESS);
    }

    /// Waits for a signal on the condvar.
    /// Returns false if it times out before a signal was received.
    #[inline]
    pub unsafe fn wait_timeout(&self, lock: &Lock, timeout: abi::timestamp) -> bool {
        let subscriptions = [
            abi::subscription {
                type_: abi::eventtype::CONDVAR,
                union: abi::subscription_union {
                    condvar: abi::subscription_condvar {
                        condvar: self.ptr(),
                        condvar_scope: abi::scope::PRIVATE,
                        lock: lock.ptr(),
                        lock_scope: abi::scope::PRIVATE,
                    },
                },
                ..mem::zeroed()
            },
            abi::subscription {
                type_: abi::eventtype::CLOCK,
                union: abi::subscription_union {
                    clock: abi::subscription_clock {
                        clock_id: abi::clockid::MONOTONIC,
                        timeout,
                        ..mem::zeroed()
                    },
                },
                ..mem::zeroed()
            },
        ];
        let mut events: [abi::event; 2] = mem::uninitialized();
        let mut nevents: usize = mem::uninitialized();
        let ret = abi::poll(subscriptions.as_ptr(), events.as_mut_ptr(), 2, &mut nevents);
        debug_assert_eq!(ret, abi::errno::SUCCESS);
        for i in 0..nevents {
            debug_assert_eq!(events[i].error, abi::errno::SUCCESS);
            if events[i].type_ == abi::eventtype::CONDVAR {
                return true;
            }
        }
        false
    }

    #[inline]
    pub unsafe fn signal(&self) {
        let ret = abi::condvar_signal(self.ptr(), abi::scope::PRIVATE, 1);
        debug_assert_eq!(ret, abi::errno::SUCCESS);
    }

    #[inline]
    fn ptr(&self) -> *mut abi::condvar {
        &self.condvar as *const AtomicU32 as *mut abi::condvar
    }
}

// Helper type for putting a thread to sleep until some other thread wakes it up
pub struct ThreadParker {
    should_park: Cell<bool>,
    lock: Lock,
    condvar: Condvar,
}

impl ThreadParker {
    pub const IS_CHEAP_TO_CONSTRUCT: bool = true;

    #[inline]
    pub fn new() -> ThreadParker {
        ThreadParker {
            should_park: Cell::new(false),
            lock: Lock::new(),
            condvar: Condvar::new(),
        }
    }

    // Prepares the parker. This should be called before adding it to the queue.
    #[inline]
    pub unsafe fn prepare_park(&self) {
        self.should_park.set(true);
    }

    // Checks if the park timed out. This should be called while holding the
    // queue lock after park_until has returned false.
    #[inline]
    pub unsafe fn timed_out(&self) -> bool {
        // We need to grab the lock here because another thread may be
        // concurrently executing UnparkHandle::unpark, which is done without
        // holding the queue lock.
        self.lock.lock();
        let should_park = self.should_park.get();
        self.lock.unlock();
        should_park
    }

    // Parks the thread until it is unparked. This should be called after it has
    // been added to the queue, after unlocking the queue.
    #[inline]
    pub unsafe fn park(&self) {
        self.lock.lock();
        while self.should_park.get() {
            self.condvar.wait(&self.lock);
        }
        self.lock.unlock();
    }

    // Parks the thread until it is unparked or the timeout is reached. This
    // should be called after it has been added to the queue, after unlocking
    // the queue. Returns true if we were unparked and false if we timed out.
    #[inline]
    pub unsafe fn park_until(&self, timeout: Instant) -> bool {
        self.lock.lock();
        while self.should_park.get() {
            if let Some(duration_left) = timeout.checked_duration_since(Instant::now()) {
                if let Ok(nanos_left) = abi::timestamp::try_from(duration_left.as_nanos()) {
                    self.condvar.wait_timeout(&self.lock, nanos_left);
                } else {
                    // remaining timeout overflows an abi::timestamp. Sleep indefinitely
                    self.condvar.wait(&self.lock);
                }
            } else {
                // We timed out
                self.lock.unlock();
                return false;
            }
        }
        self.lock.unlock();
        true
    }

    // Locks the parker to prevent the target thread from exiting. This is
    // necessary to ensure that thread-local ThreadData objects remain valid.
    // This should be called while holding the queue lock.
    #[inline]
    pub unsafe fn unpark_lock(&self) -> UnparkHandle {
        self.lock.lock();

        UnparkHandle {
            thread_parker: self,
        }
    }
}

// Handle for a thread that is about to be unparked. We need to mark the thread
// as unparked while holding the queue lock, but we delay the actual unparking
// until after the queue lock is released.
pub struct UnparkHandle {
    thread_parker: *const ThreadParker,
}

impl UnparkHandle {
    // Wakes up the parked thread. This should be called after the queue lock is
    // released to avoid blocking the queue for too long.
    #[inline]
    pub unsafe fn unpark(self) {
        (*self.thread_parker).should_park.set(false);

        // We notify while holding the lock here to avoid races with the target
        // thread. In particular, the thread could exit after we unlock the
        // mutex, which would make the condvar access invalid memory.
        (*self.thread_parker).condvar.signal();
        (*self.thread_parker).lock.unlock();
    }
}

#[inline]
pub fn thread_yield() {
    thread::yield_now();
}
