// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use core::{
    arch::wasm32,
    mem,
    sync::atomic::{AtomicUsize, Ordering},
};
use std::{convert::TryFrom, thread, time::Instant};

// Helper type for putting a thread to sleep until some other thread wakes it up
pub struct ThreadParker {
    parked: AtomicUsize,
}

const UNPARKED: usize = 0;
const PARKED: usize = 1;

impl ThreadParker {
    pub const IS_CHEAP_TO_CONSTRUCT: bool = true;

    #[inline]
    pub fn new() -> ThreadParker {
        ThreadParker {
            parked: AtomicUsize::new(UNPARKED),
        }
    }

    // Prepares the parker. This should be called before adding it to the queue.
    #[inline]
    pub fn prepare_park(&self) {
        self.parked.store(PARKED, Ordering::Relaxed);
    }

    // Checks if the park timed out. This should be called while holding the
    // queue lock after park_until has returned false.
    #[inline]
    pub fn timed_out(&self) -> bool {
        self.parked.load(Ordering::Relaxed) == PARKED
    }

    // Parks the thread until it is unparked. This should be called after it has
    // been added to the queue, after unlocking the queue.
    #[inline]
    pub fn park(&self) {
        while self.parked.load(Ordering::Acquire) == PARKED {
            let val = unsafe {
                wasm32::i32_atomic_wait(
                    ptr(&self.parked),
                    PARKED as i32, // we expect our thread is parked
                    -1,            // wait infinitely
                )
            };
            // we should have either woken up (0) or got a not-equal due to a
            // race (1). We should never time out (2)
            debug_assert!(val == 0 || val == 1);
        }
    }

    // Parks the thread until it is unparked or the timeout is reached. This
    // should be called after it has been added to the queue, after unlocking
    // the queue. Returns true if we were unparked and false if we timed out.
    #[inline]
    pub fn park_until(&self, timeout: Instant) -> bool {
        while self.parked.load(Ordering::Acquire) == PARKED {
            if let Some(left) = timeout.checked_duration_since(Instant::now()) {
                let nanos_left = i64::try_from(left.as_nanos()).unwrap_or(i64::max_value());
                unsafe {
                    wasm32::i32_atomic_wait(ptr(&self.parked), PARKED as i32, nanos_left);
                }
            } else {
                return false;
            }
        }
        true
    }

    // Locks the parker to prevent the target thread from exiting. This is
    // necessary to ensure that thread-local ThreadData objects remain valid.
    // This should be called while holding the queue lock.
    #[inline]
    pub fn unpark_lock(&self) -> UnparkHandle<'_> {
        // We don't need to lock anything, just clear the state
        self.parked.store(UNPARKED, Ordering::Release);
        UnparkHandle(&self.parked)
    }
}

// Handle for a thread that is about to be unparked. We need to mark the thread
// as unparked while holding the queue lock, but we delay the actual unparking
// until after the queue lock is released.
pub struct UnparkHandle<'a>(&'a AtomicUsize);

impl<'a> UnparkHandle<'a> {
    // Wakes up the parked thread. This should be called after the queue lock is
    // released to avoid blocking the queue for too long.
    #[inline]
    pub fn unpark(self) {
        unsafe {
            wasm32::atomic_notify(ptr(self.0), 1);
        }
    }
}

#[inline]
fn ptr(i: &AtomicUsize) -> *mut i32 {
    debug_assert_eq!(mem::size_of::<usize>(), mem::size_of::<i32>());
    i as *const AtomicUsize as *mut isize as *mut i32
}

#[inline]
pub fn thread_yield() {
    thread::yield_now();
}
