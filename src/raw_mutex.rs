// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

#[cfg(feature = "nightly")]
use std::sync::atomic::{AtomicU8, Ordering};
#[cfg(feature = "nightly")]
type U8 = u8;
#[cfg(not(feature = "nightly"))]
use stable::{AtomicU8, Ordering};
#[cfg(not(feature = "nightly"))]
type U8 = usize;
use std::thread;
use parking_lot::{self, UnparkResult};
use SPIN_LIMIT;

const LOCKED_BIT: U8 = 1;
const PARKED_BIT: U8 = 2;

pub struct RawMutex {
    state: AtomicU8,
}

impl RawMutex {
    #[cfg(feature = "nightly")]
    #[inline]
    pub const fn new() -> RawMutex {
        RawMutex { state: AtomicU8::new(0) }
    }
    #[cfg(not(feature = "nightly"))]
    #[inline]
    pub fn new() -> RawMutex {
        RawMutex { state: AtomicU8::new(0) }
    }

    #[inline]
    pub fn lock(&self) {
        if self.state
            .compare_exchange_weak(0, LOCKED_BIT, Ordering::Acquire, Ordering::Relaxed)
            .is_ok() {
            return;
        }
        self.lock_slow();
    }

    #[inline]
    pub fn try_lock(&self) -> bool {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            if state & LOCKED_BIT != 0 {
                return false;
            }
            match self.state.compare_exchange_weak(state,
                                                   state | LOCKED_BIT,
                                                   Ordering::Acquire,
                                                   Ordering::Relaxed) {
                Ok(_) => return true,
                Err(x) => state = x,
            }
        }
    }

    #[inline]
    pub fn unlock(&self) {
        if self.state
            .compare_exchange_weak(LOCKED_BIT, 0, Ordering::Release, Ordering::Relaxed)
            .is_ok() {
            return;
        }
        self.unlock_slow();
    }

    #[cold]
    #[inline(never)]
    fn lock_slow(&self) {
        let mut spin_count = 0;
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            // Grab the lock if it isn't locked, even if there is a queue on it
            if state & LOCKED_BIT == 0 {
                match self.state
                    .compare_exchange_weak(state,
                                           state | LOCKED_BIT,
                                           Ordering::Acquire,
                                           Ordering::Relaxed) {
                    Ok(_) => return,
                    Err(x) => state = x,
                }
                continue;
            }

            // If there is no queue, try spinning a few times
            if state & PARKED_BIT == 0 && spin_count < SPIN_LIMIT {
                spin_count += 1;
                thread::yield_now();
                state = self.state.load(Ordering::Relaxed);
                continue;
            }

            // Set the parked bit
            if state & PARKED_BIT == 0 {
                if let Err(x) = self.state.compare_exchange_weak(state,
                                                                 state | PARKED_BIT,
                                                                 Ordering::Relaxed,
                                                                 Ordering::Relaxed) {
                    state = x;
                    continue;
                }
            }

            // Park our thread until we are woken up by an unlock
            unsafe {
                let addr = self as *const _ as usize;
                let validate = &mut || {
                    self.state.load(Ordering::Relaxed) == LOCKED_BIT | PARKED_BIT
                };
                parking_lot::park(addr, validate, &mut || {}, None);
            }

            // Loop back and try locking again
            state = self.state.load(Ordering::Relaxed);
        }
    }

    #[cold]
    #[inline(never)]
    fn unlock_slow(&self) {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            // Unlock directly if there are no parked threads
            if state & PARKED_BIT == 0 {
                match self.state
                    .compare_exchange_weak(LOCKED_BIT, 0, Ordering::Release, Ordering::Relaxed) {
                    Ok(_) => return,
                    Err(x) => state = x,
                }
                continue;
            }

            // Unpark one thread and leave the parked bit set if there might
            // still be parked threads on this address.
            unsafe {
                let addr = self as *const _ as usize;
                let callback = &mut |result| {
                    if result == UnparkResult::UnparkedNotLast {
                        self.state.store(PARKED_BIT, Ordering::Release);
                    } else {
                        self.state.store(0, Ordering::Release);
                    }
                };
                parking_lot::unpark_one(addr, callback);
            }
            break;
        }
    }
}
