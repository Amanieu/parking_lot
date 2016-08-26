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
use parking_lot_core::{self, UnparkResult, SpinWait, DEFAULT_UNPARK_TOKEN, ParkToken, FilterOp};
use elision::{have_elision, AtomicElisionExt};

// Token indicating what type of lock queued threads are trying to acquire
const TOKEN_SHARED: ParkToken = ParkToken(0);
const TOKEN_EXCLUSIVE: ParkToken = ParkToken(1);

const PARKED_BIT: usize = 1;
const LOCKED_BIT: usize = 2;
const SHARED_COUNT_MASK: usize = !3;
const SHARED_COUNT_INC: usize = 4;

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
            .compare_exchange_weak(0, LOCKED_BIT, Ordering::Acquire, Ordering::Relaxed)
            .is_ok() {
            return;
        }
        self.lock_exclusive_slow();
    }

    #[inline]
    pub fn try_lock_exclusive(&self) -> bool {
        self.state
            .compare_exchange(0, LOCKED_BIT, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()
    }

    #[inline]
    pub fn unlock_exclusive(&self) {
        if self.state
            .compare_exchange_weak(LOCKED_BIT, 0, Ordering::Release, Ordering::Relaxed)
            .is_ok() {
            return;
        }
        self.unlock_exclusive_slow();
    }

    #[inline]
    pub fn downgrade(&self) {
        let state = self.state
            .fetch_add(SHARED_COUNT_INC - LOCKED_BIT, Ordering::Release);

        // Wake up parked shared threads if there are any
        if state & PARKED_BIT != 0 {
            self.downgrade_slow();
        }
    }

    #[inline]
    pub fn lock_shared(&self) {
        let state = self.state.load(Ordering::Relaxed);
        // Use hardware lock elision to avoid cache conflicts when multiple
        // readers try to acquire the lock. We only do this if the lock is
        // completely empty since elision handles conflicts poorly.
        if have_elision() && state == 0 {
            if self.state.elision_acquire(0, SHARED_COUNT_INC).is_ok() {
                return;
            }
        } else if let Some(new_state) = state.checked_add(SHARED_COUNT_INC) {
            if state & (LOCKED_BIT | PARKED_BIT) == 0 &&
               self.state
                .compare_exchange_weak(state, new_state, Ordering::Acquire, Ordering::Relaxed)
                .is_ok() {
                return;
            }
        }
        self.lock_shared_slow();
    }

    #[inline]
    pub fn try_lock_shared(&self) -> bool {
        let state = self.state.load(Ordering::Relaxed);

        // Even if there are no exclusive locks, we can't allow grabbing a
        // shared lock while there are parked threads since that could lead to
        // writer starvation.
        if state & (LOCKED_BIT | PARKED_BIT) != 0 {
            return false;
        }

        // Use hardware lock elision to avoid cache conflicts when multiple
        // readers try to acquire the lock. We only do this if the lock is
        // completely empty since elision handles conflicts poorly.
        if have_elision() && state == 0 {
            if self.state.elision_acquire(0, SHARED_COUNT_INC).is_ok() {
                return true;
            }
        } else if let Some(new_state) = state.checked_add(SHARED_COUNT_INC) {
            if self.state
                .compare_exchange_weak(state, new_state, Ordering::Acquire, Ordering::Relaxed)
                .is_ok() {
                return true;
            }
        }
        self.try_lock_shared_slow()
    }

    #[inline]
    pub fn unlock_shared(&self) {
        let state = self.state.load(Ordering::Relaxed);
        if state & PARKED_BIT == 0 || state & SHARED_COUNT_MASK != SHARED_COUNT_INC {
            if have_elision() {
                if self.state.elision_release(state, state - SHARED_COUNT_INC).is_ok() {
                    return;
                }
            } else {
                if self.state
                    .compare_exchange_weak(state,
                                           state - SHARED_COUNT_INC,
                                           Ordering::Release,
                                           Ordering::Relaxed)
                    .is_ok() {
                    return;
                }
            }
        }
        self.unlock_shared_slow();
    }

    #[cold]
    #[inline(never)]
    fn lock_exclusive_slow(&self) {
        let mut spinwait = SpinWait::new();
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            // Grab the lock if it isn't locked, even if there are other
            // threads parked.
            if state & (LOCKED_BIT | SHARED_COUNT_MASK) == 0 {
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

            // If there are no parked threads and only one reader or writer, try
            // spinning a few times.
            if state & PARKED_BIT == 0 &&
               (state & LOCKED_BIT != 0 || state & SHARED_COUNT_MASK == SHARED_COUNT_INC) &&
               spinwait.spin() {
                state = self.state.load(Ordering::Relaxed);
                continue;
            }

            // Park our thread until we are woken up by an unlock
            unsafe {
                let addr = self as *const _ as usize;
                let validate = || {
                    let mut state = self.state.load(Ordering::Relaxed);
                    loop {
                        // If the rwlock is free, abort the park and try to grab
                        // it immediately.
                        if state & (LOCKED_BIT | SHARED_COUNT_MASK) == 0 {
                            return false;
                        }

                        // Nothing to do if the parked bit is already set
                        if state & PARKED_BIT != 0 {
                            return true;
                        }

                        // Set the parked bit
                        match self.state.compare_exchange_weak(state,
                                                               state | PARKED_BIT,
                                                               Ordering::Relaxed,
                                                               Ordering::Relaxed) {
                            Ok(_) => return true,
                            Err(x) => state = x,
                        }
                    }
                };
                let before_sleep = || {};
                let timed_out = |_, _| unreachable!();
                parking_lot_core::park(addr,
                                       validate,
                                       before_sleep,
                                       timed_out,
                                       TOKEN_EXCLUSIVE,
                                       None);
            }

            // Loop back and try locking again
            spinwait.reset();
            state = self.state.load(Ordering::Relaxed);
        }
    }

    #[cold]
    #[inline(never)]
    fn unlock_exclusive_slow(&self) {
        // Unlock directly if there are no parked threads
        if self.state
            .compare_exchange(LOCKED_BIT, 0, Ordering::Release, Ordering::Relaxed)
            .is_ok() {
            return;
        }

        // There are threads to unpark. We can unpark a single exclusive
        // thread or many shared threads.
        let mut first_token = None;
        unsafe {
            let addr = self as *const _ as usize;
            let filter = |token| -> FilterOp {
                if let Some(first_token) = first_token {
                    if first_token == TOKEN_EXCLUSIVE || token != first_token {
                        FilterOp::Stop
                    } else {
                        FilterOp::Unpark
                    }
                } else {
                    first_token = Some(token);
                    FilterOp::Unpark
                }
            };
            let callback = |result: UnparkResult| {
                // Clear the locked bit, and the parked bit as well if there
                // are no more parked threads.
                if result.have_more_threads {
                    self.state.store(PARKED_BIT, Ordering::Release);
                } else {
                    self.state.store(0, Ordering::Release);
                }
                DEFAULT_UNPARK_TOKEN
            };
            parking_lot_core::unpark_filter(addr, filter, callback);
        }
    }

    #[cold]
    #[inline(never)]
    fn downgrade_slow(&self) {
        // Unpark shared threads only
        unsafe {
            let addr = self as *const _ as usize;
            let filter = |token| -> FilterOp {
                if token == TOKEN_SHARED {
                    FilterOp::Unpark
                } else {
                    FilterOp::Stop
                }
            };
            let callback = |result: UnparkResult| {
                // Clear the parked bit if there no more parked threads
                if !result.have_more_threads {
                    self.state.fetch_and(!PARKED_BIT, Ordering::Relaxed);
                }
                DEFAULT_UNPARK_TOKEN
            };
            parking_lot_core::unpark_filter(addr, filter, callback);
        }
    }

    #[cold]
    #[inline(never)]
    fn lock_shared_slow(&self) {
        let mut spinwait = SpinWait::new();
        let mut spinwait_shared = SpinWait::new();
        let mut state = self.state.load(Ordering::Relaxed);
        let mut unparked = false;
        loop {
            // Use hardware lock elision to avoid cache conflicts when multiple
            // readers try to acquire the lock. We only do this if the lock is
            // completely empty since elision handles conflicts poorly.
            if have_elision() && state == 0 {
                match self.state.elision_acquire(0, SHARED_COUNT_INC) {
                    Ok(_) => return,
                    Err(x) => state = x,
                }
            }

            // Grab the lock if there are no exclusive threads locked or
            // waiting. However if we were unparked then we are allowed to grab
            // the lock even if there are pending exclusive threads.
            if state & LOCKED_BIT == 0 && (unparked || state & PARKED_BIT == 0) {
                let new = state.checked_add(SHARED_COUNT_INC)
                    .expect("RwLock shared count overflow");
                if self.state
                    .compare_exchange_weak(state, new, Ordering::Acquire, Ordering::Relaxed)
                    .is_ok() {
                    return;
                }

                // If there is high contention on the reader count then we want
                // to leave some time between attempts to acquire the lock to
                // let other threads make progress.
                spinwait_shared.spin_no_yield();
                state = self.state.load(Ordering::Relaxed);
                continue;
            }

            // If there are no parked threads, try spinning a few times
            if state & PARKED_BIT == 0 && spinwait.spin() {
                state = self.state.load(Ordering::Relaxed);
                continue;
            }

            // Park our thread until we are woken up by an unlock
            unsafe {
                let addr = self as *const _ as usize;
                let validate = || {
                    let mut state = self.state.load(Ordering::Relaxed);
                    loop {
                        // Nothing to do if the parked bit is already set
                        if state & PARKED_BIT != 0 {
                            return true;
                        }

                        // If the parked bit is not set then it means we are at
                        // the front of the queue. If there is no exclusive lock
                        // then we should abort the park and try acquiring the
                        // lock again.
                        if state & LOCKED_BIT == 0 {
                            return false;
                        }

                        // Set the parked bit
                        match self.state.compare_exchange_weak(state,
                                                               state | PARKED_BIT,
                                                               Ordering::Relaxed,
                                                               Ordering::Relaxed) {
                            Ok(_) => return true,
                            Err(x) => state = x,
                        }
                    }
                };
                let before_sleep = || {};
                let timed_out = |_, _| unreachable!();
                parking_lot_core::park(addr, validate, before_sleep, timed_out, TOKEN_SHARED, None);
            }

            // Loop back and try locking again
            spinwait.reset();
            spinwait_shared.reset();
            state = self.state.load(Ordering::Relaxed);
            unparked = true;
        }
    }

    #[cold]
    #[inline(never)]
    pub fn try_lock_shared_slow(&self) -> bool {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            if state & (LOCKED_BIT | PARKED_BIT) != 0 {
                return false;
            }
            if have_elision() && state == 0 {
                match self.state.elision_acquire(0, SHARED_COUNT_INC) {
                    Ok(_) => return true,
                    Err(x) => state = x,
                }
            } else {
                let new = state.checked_add(SHARED_COUNT_INC)
                    .expect("RwLock shared count overflow");
                match self.state
                    .compare_exchange_weak(state, new, Ordering::Acquire, Ordering::Relaxed) {
                    Ok(_) => return true,
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
            // Just release the lock if there are no parked thread or if we are
            // not the last shared thread.
            if state & PARKED_BIT == 0 || state & SHARED_COUNT_MASK != SHARED_COUNT_INC {
                match self.state
                    .compare_exchange_weak(state,
                                           state - SHARED_COUNT_INC,
                                           Ordering::Release,
                                           Ordering::Relaxed) {
                    Ok(_) => return,
                    Err(x) => state = x,
                }
                continue;
            }

            // There are exclusive threads to unpark. We shouldn't have a case
            // where we have shared threads at the front of the queue.
            let mut first = true;
            unsafe {
                let addr = self as *const _ as usize;
                let filter = |token| -> FilterOp {
                    if !first {
                        FilterOp::Stop
                    } else {
                        // The check in lock_shared_slow guarantees that a
                        // shared thread will not get parked if it is at the
                        // front of the queue and there is no exclusive lock.
                        debug_assert!(token == TOKEN_EXCLUSIVE);
                        first = false;
                        FilterOp::Unpark
                    }
                };
                let callback = |result: UnparkResult| {
                    // Release the shared lock and clear the parked bit if there
                    // are no more parked threads.
                    let mut state = self.state.load(Ordering::Relaxed);
                    loop {
                        let mut new = state - SHARED_COUNT_INC;
                        if !result.have_more_threads {
                            new &= !PARKED_BIT;
                        }
                        match self.state
                            .compare_exchange_weak(state,
                                                   new,
                                                   Ordering::Release,
                                                   Ordering::Relaxed) {
                            Ok(_) => break,
                            Err(x) => state = x,
                        }
                    }
                    DEFAULT_UNPARK_TOKEN
                };
                parking_lot_core::unpark_filter(addr, filter, callback);
            }
            break;
        }
    }
}
