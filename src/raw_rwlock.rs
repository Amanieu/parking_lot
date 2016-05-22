// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

#[cfg(feature = "nightly")]
use std::sync::atomic::{AtomicUsize, Ordering};
#[cfg(not(feature = "nightly"))]
use stable::{AtomicUsize, Ordering};
use std::thread;
use parking_lot::{self, UnparkResult};
use SPIN_LIMIT;

const SHARED_PARKED_BIT: usize = 1;
const EXCLUSIVE_PARKED_BIT: usize = 2;
const EXCLUSIVE_LOCKED_BIT: usize = 4;
const SHARED_COUNT_MASK: usize = !7;
const SHARED_COUNT_INC: usize = 8;

pub struct RawRwLock {
    state: AtomicUsize,
}

impl RawRwLock {
    #[cfg(feature = "nightly")]
    #[inline]
    pub const fn new() -> RawRwLock {
        RawRwLock { state: AtomicUsize::new(0) }
    }
    #[cfg(not(feature = "nightly"))]
    #[inline]
    pub fn new() -> RawRwLock {
        RawRwLock { state: AtomicUsize::new(0) }
    }

    #[inline]
    pub fn lock_exclusive(&self) {
        if self.state
            .compare_exchange_weak(0,
                                   EXCLUSIVE_LOCKED_BIT,
                                   Ordering::Acquire,
                                   Ordering::Relaxed)
            .is_ok() {
            return;
        }
        self.lock_exclusive_slow();
    }

    #[inline]
    pub fn try_lock_exclusive(&self) -> bool {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            if state & (EXCLUSIVE_LOCKED_BIT | SHARED_COUNT_MASK) != 0 {
                return false;
            }
            match self.state.compare_exchange_weak(state,
                                                   state | EXCLUSIVE_LOCKED_BIT,
                                                   Ordering::Acquire,
                                                   Ordering::Relaxed) {
                Ok(_) => return true,
                Err(x) => state = x,
            }
        }
    }

    #[inline]
    pub fn unlock_exclusive(&self) {
        if self.state
            .compare_exchange_weak(EXCLUSIVE_LOCKED_BIT,
                                   0,
                                   Ordering::Release,
                                   Ordering::Relaxed)
            .is_ok() {
            return;
        }
        self.unlock_exclusive_slow();
    }

    #[inline]
    pub fn lock_shared(&self) {
        let state = self.state.load(Ordering::Relaxed);
        if state & (EXCLUSIVE_LOCKED_BIT | EXCLUSIVE_PARKED_BIT) == 0 &&
           self.state
            .compare_exchange_weak(state,
                                   state.checked_add(SHARED_COUNT_INC)
                                       .expect("RwLock shared count overflow"),
                                   Ordering::Acquire,
                                   Ordering::Relaxed)
            .is_ok() {
            return;
        }
        self.lock_shared_slow();
    }

    #[inline]
    pub fn try_lock_shared(&self) -> bool {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            if state & (EXCLUSIVE_LOCKED_BIT | EXCLUSIVE_PARKED_BIT) != 0 {
                return false;
            }
            match self.state.compare_exchange_weak(state,
                                                   state.checked_add(SHARED_COUNT_INC)
                                                       .expect("RwLock shared count overflow"),
                                                   Ordering::Acquire,
                                                   Ordering::Relaxed) {
                Ok(_) => return true,
                Err(x) => state = x,
            }
        }
    }

    #[inline]
    pub fn unlock_shared(&self) {
        let state = self.state.load(Ordering::Relaxed);
        if (state & EXCLUSIVE_PARKED_BIT == 0 || state & SHARED_COUNT_MASK != SHARED_COUNT_INC) &&
           self.state
            .compare_exchange_weak(state,
                                   state - SHARED_COUNT_INC,
                                   Ordering::Release,
                                   Ordering::Relaxed)
            .is_ok() {
            return;
        }
        self.unlock_shared_slow();
    }

    #[cold]
    #[inline(never)]
    fn lock_exclusive_slow(&self) {
        let mut spin_count = 0;
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            // Grab the lock if it isn't locked, even if there are other
            // threads parked.
            if state & (EXCLUSIVE_LOCKED_BIT | SHARED_COUNT_MASK) == 0 {
                match self.state
                    .compare_exchange_weak(state,
                                           state | EXCLUSIVE_LOCKED_BIT,
                                           Ordering::Acquire,
                                           Ordering::Relaxed) {
                    Ok(_) => return,
                    Err(x) => state = x,
                }
                continue;
            }

            // If there are no parked exclusive threads and only one reader or
            // writer, try spinning a few times.
            if state & EXCLUSIVE_PARKED_BIT == 0 &&
               (state & EXCLUSIVE_LOCKED_BIT != 0 ||
                state & SHARED_COUNT_MASK == SHARED_COUNT_INC) &&
               spin_count < SPIN_LIMIT {
                spin_count += 1;
                thread::yield_now();
                state = self.state.load(Ordering::Relaxed);
                continue;
            }

            // Set the parked bit
            if state & EXCLUSIVE_PARKED_BIT == 0 {
                if let Err(x) = self.state.compare_exchange_weak(state,
                                                                 state | EXCLUSIVE_PARKED_BIT,
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
                    let state = self.state.load(Ordering::Relaxed);
                    state & EXCLUSIVE_PARKED_BIT != 0 &&
                    state & (EXCLUSIVE_LOCKED_BIT | SHARED_COUNT_MASK) != 0
                };
                let before_sleep = &mut || {};
                let timed_out = &mut |_, _| unreachable!();
                parking_lot::park(addr, validate, before_sleep, timed_out, None);
            }

            // Loop back and try locking again
            state = self.state.load(Ordering::Relaxed);
        }
    }

    #[cold]
    #[inline(never)]
    fn unlock_exclusive_slow(&self) {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            // Unlock directly if there are no parked threads
            if state & (EXCLUSIVE_PARKED_BIT | SHARED_PARKED_BIT) == 0 {
                match self.state
                    .compare_exchange_weak(EXCLUSIVE_LOCKED_BIT,
                                           0,
                                           Ordering::Release,
                                           Ordering::Relaxed) {
                    Ok(_) => return,
                    Err(x) => state = x,
                }
                continue;
            }

            // If there are exclusive parked threads, wake one of them up.
            if state & EXCLUSIVE_PARKED_BIT != 0 {
                unsafe {
                    let addr = self as *const _ as usize;
                    let callback = &mut |result| {
                        // Clear the exclusive parked bit if this was the last
                        // exclusive thread. Also clear the locked bit if we
                        // successfully unparked a thread.
                        match result {
                            UnparkResult::UnparkedNotLast => {
                                self.state.fetch_and(!EXCLUSIVE_LOCKED_BIT, Ordering::Release)
                            }
                            UnparkResult::UnparkedLast => {
                                self.state
                                    .fetch_and(!(EXCLUSIVE_PARKED_BIT | EXCLUSIVE_LOCKED_BIT),
                                               Ordering::Release)
                            }
                            UnparkResult::NoParkedThreads => {
                                self.state.fetch_and(!EXCLUSIVE_PARKED_BIT, Ordering::Relaxed)
                            }
                        };
                    };
                    if parking_lot::unpark_one(addr, callback) != UnparkResult::NoParkedThreads {
                        // If we successfully unparked an exclusive thread,
                        // stop here.
                        return;
                    }
                }
            }

            // Release the exclusive lock and clear the shared parked bit
            if let Err(x) = self.state
                .compare_exchange_weak(EXCLUSIVE_LOCKED_BIT | SHARED_PARKED_BIT,
                                       0,
                                       Ordering::Release,
                                       Ordering::Relaxed) {
                state = x;
                continue;
            }

            // Unpark all waiting shared threads.
            unsafe {
                let addr = self as *const _ as usize;
                parking_lot::unpark_all(addr + 1);
            }
            break;
        }
    }

    #[cold]
    #[inline(never)]
    fn lock_shared_slow(&self) {
        let mut spin_count = 0;
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            // Grab the lock if there are no exclusive threads locked or waiting
            if state & (EXCLUSIVE_LOCKED_BIT | EXCLUSIVE_PARKED_BIT) == 0 {
                match self.state
                    .compare_exchange_weak(state,
                                           state.checked_add(SHARED_COUNT_INC)
                                               .expect("RwLock shared count overflow"),
                                           Ordering::Acquire,
                                           Ordering::Relaxed) {
                    Ok(_) => return,
                    Err(x) => state = x,
                }
                continue;
            }

            // If there are no parked exclusive threads, try spinning a few
            // times
            if state & EXCLUSIVE_PARKED_BIT == 0 && spin_count < SPIN_LIMIT {
                spin_count += 1;
                thread::yield_now();
                state = self.state.load(Ordering::Relaxed);
                continue;
            }

            // Set the shared parked bit
            if state & SHARED_PARKED_BIT == 0 {
                if let Err(x) = self.state.compare_exchange_weak(state,
                                                                 state | SHARED_PARKED_BIT,
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
                    let state = self.state.load(Ordering::Relaxed);
                    state & SHARED_PARKED_BIT != 0 &&
                    state & (EXCLUSIVE_LOCKED_BIT | EXCLUSIVE_PARKED_BIT) != 0
                };
                let before_sleep = &mut || {};
                let timed_out = &mut |_, _| unreachable!();
                parking_lot::park(addr + 1, validate, before_sleep, timed_out, None);
            }

            // Loop back and try locking again
            state = self.state.load(Ordering::Relaxed);
        }
    }

    #[cold]
    #[inline(never)]
    fn unlock_shared_slow(&self) {
        // Decrement the shared lock count
        let mut state = self.state.fetch_sub(SHARED_COUNT_INC, Ordering::Release) -
                        SHARED_COUNT_INC;

        // If this was the last shared thread and there are exclusive parked
        // threads then wake one up.
        if state & EXCLUSIVE_PARKED_BIT != 0 && state & SHARED_COUNT_MASK == 0 {
            unsafe {
                let addr = self as *const _ as usize;
                let callback = &mut |result| {
                    // Clear the exclusive parked bit if this was the last
                    // exclusive thread
                    if result != UnparkResult::UnparkedNotLast {
                        self.state.fetch_and(!EXCLUSIVE_PARKED_BIT, Ordering::Relaxed);
                    }
                };
                if parking_lot::unpark_one(addr, callback) != UnparkResult::NoParkedThreads {
                    // If we successfully unparked an exclusive thread,
                    // stop here.
                    return;
                }

                state = self.state.load(Ordering::Relaxed);
            }
        }

        // If there are any shared parked threads and no parked exclusive
        // threads then unparked all shared threads.
        if state & EXCLUSIVE_PARKED_BIT == 0 && state & SHARED_PARKED_BIT != 0 {
            if self.state.fetch_and(!SHARED_PARKED_BIT, Ordering::Relaxed) & SHARED_PARKED_BIT !=
               0 {
                unsafe {
                    let addr = self as *const _ as usize;
                    parking_lot::unpark_all(addr + 1);
                }
            }
        }
    }
}
