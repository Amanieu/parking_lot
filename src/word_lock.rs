// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;
use std::ptr;
use std::mem;
use std::cell::Cell;
use thread_parker::ThreadParker;
use SPIN_LIMIT;

struct ThreadData {
    parker: ThreadParker,
    next_in_queue: Cell<*const ThreadData>,

    // To make everything fit in 1 word we cheat by putting the tail pointer of
    // the linked list in the first element of the queue.
    queue_tail: Cell<*const ThreadData>,
}

impl ThreadData {
    fn new() -> ThreadData {
        ThreadData {
            parker: ThreadParker::new(),
            next_in_queue: Cell::new(ptr::null()),
            queue_tail: Cell::new(ptr::null()),
        }
    }
}

thread_local!(static THREAD_DATA: ThreadData = ThreadData::new());

const LOCKED_BIT: usize = 1;
const QUEUE_LOCKED_BIT: usize = 2;
const QUEUE_MASK: usize = !3;

// Word-sized lock that is used to implement the parking_lot API. Since this
// can't used parking_lot, it instead manages its own queue of waiting threads.
pub struct WordLock {
    state: AtomicUsize,
}

impl WordLock {
    #[inline]
    pub const fn new() -> WordLock {
        WordLock { state: AtomicUsize::new(0) }
    }

    #[inline]
    pub unsafe fn lock(&self) {
        if self.state
            .compare_exchange_weak(0, LOCKED_BIT, Ordering::Acquire, Ordering::Relaxed)
            .is_ok() {
            return;
        }
        self.lock_slow();
    }

    #[inline]
    pub unsafe fn unlock(&self) {
        if self.state
            .compare_exchange_weak(LOCKED_BIT, 0, Ordering::Release, Ordering::Relaxed)
            .is_ok() {
            return;
        }
        self.unlock_slow();
    }

    #[inline(never)]
    unsafe fn lock_slow(&self) {
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
            if state & QUEUE_MASK == 0 && spin_count < SPIN_LIMIT {
                spin_count += 1;
                thread::yield_now();
                state = self.state.load(Ordering::Relaxed);
                continue;
            }

            // Spin if the queue is locked
            if state & QUEUE_LOCKED_BIT != 0 {
                thread::yield_now();
                state = self.state.load(Ordering::Relaxed);
                continue;
            }

            // Try locking the queue
            if let Err(x) = self.state
                .compare_exchange_weak(state,
                                       state | QUEUE_LOCKED_BIT,
                                       Ordering::Acquire,
                                       Ordering::Relaxed) {
                state = x;
                continue;
            }

            // Get our thread data
            THREAD_DATA.with(|thread_data| {
                assert!(mem::align_of_val(thread_data) > !QUEUE_MASK);

                // Add our thread to the queue and unlock the queue
                thread_data.next_in_queue.set(ptr::null());
                thread_data.parker.prepare_park();
                let mut queue_head = (state & QUEUE_MASK) as *const ThreadData;
                if !queue_head.is_null() {
                    (*(*queue_head).queue_tail.get()).next_in_queue.set(thread_data);
                } else {
                    queue_head = thread_data;
                }
                (*queue_head).queue_tail.set(thread_data);
                self.state.store((queue_head as usize) | LOCKED_BIT, Ordering::Release);

                // Sleep until we are woken up by an unlock
                thread_data.parker.park();
            });

            self.state.load(Ordering::Relaxed);
        }
    }

    #[inline(never)]
    unsafe fn unlock_slow(&self) {
        let queue_head;
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            // Unlock directly if there is no queue
            if state == LOCKED_BIT {
                match self.state
                    .compare_exchange_weak(LOCKED_BIT, 0, Ordering::Release, Ordering::Relaxed) {
                    Ok(_) => return,
                    Err(x) => state = x,
                }
                continue;
            }

            // Spin if the queue is locked
            if state & QUEUE_LOCKED_BIT != 0 {
                thread::yield_now();
                state = self.state.load(Ordering::Relaxed);
                continue;
            }

            // Try locking the queue
            match self.state
                .compare_exchange_weak(state,
                                       state | QUEUE_LOCKED_BIT,
                                       Ordering::Acquire,
                                       Ordering::Relaxed) {
                Ok(_) => {
                    queue_head = (state & QUEUE_MASK) as *mut ThreadData;
                    break;
                }
                Err(x) => state = x,
            }
        }

        // At this point the queue is locked and must be non-empty. First remove
        // the first entry in the queue.
        let new_queue_head = (*queue_head).next_in_queue.get();
        if !new_queue_head.is_null() {
            (*new_queue_head).queue_tail.set((*queue_head).queue_tail.get());
        }
        self.state.store(new_queue_head as usize, Ordering::Release);

        // Then wake up the thread we removed from the queue
        (*queue_head).parker.unpark();
    }
}
