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
use spinwait::SpinWait;
use parking_lot::{self, UnparkResult};
use elision::{have_elision, AtomicElisionExt};
use poison::Poison;

const POISON_BIT: usize = 1;
const SHARED_PARKED_BIT: usize = 2;
const EXCLUSIVE_PARKED_BIT: usize = 4;
const EXCLUSIVE_LOCKED_BIT: usize = 8;
const SHARED_COUNT_MASK: usize = !15;
const SHARED_COUNT_INC: usize = 16;

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
    pub fn lock_exclusive(&self) -> Poison {
        if self.state
            .compare_exchange_weak(0,
                                   EXCLUSIVE_LOCKED_BIT,
                                   Ordering::Acquire,
                                   Ordering::Relaxed)
            .is_ok() {
            return Poison(false);
        }
        self.lock_exclusive_slow()
    }

    #[inline]
    pub fn try_lock_exclusive(&self) -> Option<Poison> {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            if state & (EXCLUSIVE_LOCKED_BIT | SHARED_COUNT_MASK) != 0 {
                return None;
            }
            match self.state.compare_exchange_weak(state,
                                                   state | EXCLUSIVE_LOCKED_BIT,
                                                   Ordering::Acquire,
                                                   Ordering::Relaxed) {
                Ok(_) => return Some(Poison(state & POISON_BIT != 0)),
                Err(x) => state = x,
            }
        }
    }

    #[inline]
    pub fn unlock_exclusive(&self, poison: Poison) {
        if !poison.0 &&
           self.state
            .compare_exchange_weak(EXCLUSIVE_LOCKED_BIT,
                                   0,
                                   Ordering::Release,
                                   Ordering::Relaxed)
            .is_ok() {
            return;
        }
        self.unlock_exclusive_slow(poison);
    }

    #[inline]
    pub fn lock_shared(&self) -> Poison {
        let state = self.state.load(Ordering::Relaxed);
        // Use hardware lock elision to avoid cache conflicts when multiple
        // readers try to acquire the lock. We only do this if the lock is
        // completely empty since elision handles conflicts poorly.
        if have_elision() && state == 0 {
            if self.state.elision_acquire(0, SHARED_COUNT_INC).is_ok() {
                return Poison(false);
            }
        } else if let Some(new_state) = state.checked_add(SHARED_COUNT_INC) {
            if state & (POISON_BIT | EXCLUSIVE_LOCKED_BIT | EXCLUSIVE_PARKED_BIT) == 0 &&
               self.state
                .compare_exchange_weak(state, new_state, Ordering::Acquire, Ordering::Relaxed)
                .is_ok() {
                return Poison(false);
            }
        }
        self.lock_shared_slow()
    }

    #[inline]
    pub fn try_lock_shared(&self) -> Option<Poison> {
        let state = self.state.load(Ordering::Relaxed);
        if state & (EXCLUSIVE_LOCKED_BIT | EXCLUSIVE_PARKED_BIT) != 0 {
            return None;
        }
        // Use hardware lock elision to avoid cache conflicts when multiple
        // readers try to acquire the lock. We only do this if the lock is
        // completely empty since elision handles conflicts poorly.
        if have_elision() && state == 0 {
            if self.state.elision_acquire(0, SHARED_COUNT_INC).is_ok() {
                return Some(Poison(false));
            }
        } else if let Some(new_state) = state.checked_add(SHARED_COUNT_INC) {
            if state & (POISON_BIT | EXCLUSIVE_LOCKED_BIT | EXCLUSIVE_PARKED_BIT) == 0 &&
               self.state
                .compare_exchange_weak(state, new_state, Ordering::Acquire, Ordering::Relaxed)
                .is_ok() {
                return Some(Poison(false));
            }
        }
        self.try_lock_shared_slow()
    }

    #[inline]
    pub fn unlock_shared(&self) {
        let state = self.state.load(Ordering::Relaxed);
        // Release the elided lock here. If we elided the lock then it will look
        // as if we are the only reader on it.
        if have_elision() && state == SHARED_COUNT_INC {
            if self.state.elision_release(SHARED_COUNT_INC, 0).is_ok() {
                return;
            }
        } else {
            if (state & EXCLUSIVE_PARKED_BIT == 0 ||
                state & SHARED_COUNT_MASK != SHARED_COUNT_INC) &&
               self.state
                .compare_exchange_weak(state,
                                       state - SHARED_COUNT_INC,
                                       Ordering::Release,
                                       Ordering::Relaxed)
                .is_ok() {
                return;

            }
        }
        self.unlock_shared_slow();
    }

    #[inline]
    pub fn is_poisoned(&self) -> Poison {
        Poison(self.state.load(Ordering::Relaxed) & POISON_BIT != 0)
    }

    #[cold]
    #[inline(never)]
    fn lock_exclusive_slow(&self) -> Poison {
        let mut spinwait = SpinWait::new();
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
                    Ok(_) => return Poison(state & POISON_BIT != 0),
                    Err(x) => state = x,
                }
                continue;
            }

            // If there are no parked exclusive threads and only one reader or
            // writer, try spinning a few times.
            if state & EXCLUSIVE_PARKED_BIT == 0 &&
               (state & EXCLUSIVE_LOCKED_BIT != 0 ||
                state & SHARED_COUNT_MASK == SHARED_COUNT_INC) && spinwait.spin() {
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
            spinwait.reset();
            state = self.state.load(Ordering::Relaxed);
        }
    }

    #[cold]
    #[inline(never)]
    fn unlock_exclusive_slow(&self, poison: Poison) {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            let poison_bit = if poison.0 {
                POISON_BIT
            } else {
                state & POISON_BIT
            };

            // Unlock directly if there are no parked threads
            if state & (EXCLUSIVE_PARKED_BIT | SHARED_PARKED_BIT) == 0 {
                match self.state
                    .compare_exchange_weak(state,
                                           poison_bit,
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
                        // Set the poison bit before unlocking
                        if poison.0 && result != UnparkResult::NoParkedThreads {
                            self.state.fetch_or(POISON_BIT, Ordering::Relaxed);
                        }

                        // Clear the exclusive parked bit if this was the last
                        // exclusive thread. Also clear the locked bit if we
                        // successfully unparked a thread.
                        let mask = match result {
                            UnparkResult::UnparkedNotLast => !EXCLUSIVE_LOCKED_BIT,
                            UnparkResult::UnparkedLast => {
                                !(EXCLUSIVE_PARKED_BIT | EXCLUSIVE_LOCKED_BIT)
                            }
                            UnparkResult::NoParkedThreads => !EXCLUSIVE_PARKED_BIT,
                        };
                        state = self.state.fetch_and(mask, Ordering::Release);
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
                .compare_exchange_weak(state & !EXCLUSIVE_PARKED_BIT,
                                       poison_bit,
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
    fn lock_shared_slow(&self) -> Poison {
        let mut spinwait = SpinWait::new();
        let mut spinwait_shared = SpinWait::new();
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            // Grab the lock if there are no exclusive threads locked or waiting
            if state & (EXCLUSIVE_LOCKED_BIT | EXCLUSIVE_PARKED_BIT) == 0 {
                if have_elision() && state == 0 {
                    if self.state.elision_acquire(0, SHARED_COUNT_INC).is_ok() {
                        return Poison(state & POISON_BIT != 0);
                    }
                } else {
                    if self.state
                        .compare_exchange_weak(state,
                                               state.checked_add(SHARED_COUNT_INC)
                                                   .expect("RwLock shared count overflow"),
                                               Ordering::Acquire,
                                               Ordering::Relaxed)
                        .is_ok() {
                        return Poison(state & POISON_BIT != 0);
                    }
                }

                // If there is high contention on the reader count then we want
                // to leave some time between attempts to acquire the lock to
                // let other threads make progress.
                spinwait_shared.spin_no_yield();
                state = self.state.load(Ordering::Relaxed);
                continue;
            }

            // If there are no parked exclusive threads, try spinning a few
            // times
            if state & EXCLUSIVE_PARKED_BIT == 0 && spinwait.spin() {
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
            spinwait.reset();
            spinwait_shared.reset();
            state = self.state.load(Ordering::Relaxed);
        }
    }

    #[cold]
    #[inline(never)]
    pub fn try_lock_shared_slow(&self) -> Option<Poison> {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            if state & (EXCLUSIVE_LOCKED_BIT | EXCLUSIVE_PARKED_BIT) != 0 {
                return None;
            }
            if have_elision() && state == 0 {
                match self.state.elision_acquire(0, SHARED_COUNT_INC) {
                    Ok(_) => return Some(Poison(state & POISON_BIT != 0)),
                    Err(x) => state = x,
                }
            } else {
                match self.state.compare_exchange_weak(state,
                                                       state.checked_add(SHARED_COUNT_INC)
                                                           .expect("RwLock shared count \
                                                                    overflow"),
                                                       Ordering::Acquire,
                                                       Ordering::Relaxed) {
                    Ok(_) => return Some(Poison(state & POISON_BIT != 0)),
                    Err(x) => state = x,
                }
            }
        }
    }

    #[cold]
    #[inline(never)]
    fn unlock_shared_slow(&self) {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            // If this is the last shared thread and there are exclusive parked
            // threads then wake one up.
            if state & EXCLUSIVE_PARKED_BIT != 0 && state & SHARED_COUNT_MASK == SHARED_COUNT_INC {
                unsafe {
                    let addr = self as *const _ as usize;
                    let callback = &mut |result| {
                        // Clear the exclusive parked bit if this was the last
                        // exclusive thread.
                        loop {
                            let mut new_state = state;
                            if result != UnparkResult::NoParkedThreads {
                                new_state -= SHARED_COUNT_INC;
                            }
                            if result != UnparkResult::UnparkedNotLast {
                                new_state &= !EXCLUSIVE_PARKED_BIT;
                            }
                            match self.state.compare_exchange_weak(state,
                                                                   new_state,
                                                                   Ordering::Release,
                                                                   Ordering::Relaxed) {
                                Ok(_) => {
                                    state = new_state;
                                    return;
                                }
                                Err(x) => state = x,
                            }
                        }
                    };
                    if parking_lot::unpark_one(addr, callback) != UnparkResult::NoParkedThreads {
                        // If we successfully unparked an exclusive thread,
                        // stop here.
                        return;
                    }
                }
            }

            // Release the shared lock and clear the shared parked bit if there
            // are no pending exclusive threads.
            let mut new_state = state - SHARED_COUNT_INC;
            if state & EXCLUSIVE_PARKED_BIT == 0 {
                new_state &= !SHARED_PARKED_BIT;
            }
            if let Err(x) = self.state
                .compare_exchange_weak(state, new_state, Ordering::Release, Ordering::Relaxed) {
                state = x;
                continue;
            }

            // If there are any shared parked threads and no parked exclusive
            // threads then unpark all shared threads.
            if state & EXCLUSIVE_PARKED_BIT == 0 && state & SHARED_PARKED_BIT != 0 {
                unsafe {
                    let addr = self as *const _ as usize;
                    parking_lot::unpark_all(addr + 1);
                }
            }
            break;
        }
    }
}
