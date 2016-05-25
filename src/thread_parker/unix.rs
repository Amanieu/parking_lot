// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use std::cell::{Cell, UnsafeCell};
use std::time::{Instant, SystemTime, UNIX_EPOCH};
use libc;

// Helper type for putting a thread to sleep until some other thread wakes it up
pub struct ThreadParker {
    should_park: Cell<bool>,
    mutex: UnsafeCell<libc::pthread_mutex_t>,
    condvar: UnsafeCell<libc::pthread_cond_t>,
}

impl ThreadParker {
    pub fn new() -> ThreadParker {
        ThreadParker {
            should_park: Cell::new(false),
            mutex: UnsafeCell::new(libc::PTHREAD_MUTEX_INITIALIZER),
            condvar: UnsafeCell::new(libc::PTHREAD_COND_INITIALIZER),
        }
    }

    // Prepares the parker. This should be called before adding it to the queue.
    pub unsafe fn prepare_park(&self) {
        self.should_park.set(true);
    }

    // Checks if the park timed out. This should be called while holding the
    // queue lock after park_until has returned false.
    pub unsafe fn timed_out(&self) -> bool {
        self.should_park.get()
    }

    // Parks the thread until it is unparked. This should be called after it has
    // been added to the queue, after unlocking the queue.
    pub unsafe fn park(&self) {
        let r = libc::pthread_mutex_lock(self.mutex.get());
        debug_assert_eq!(r, 0);
        while self.should_park.get() {
            let r = libc::pthread_cond_wait(self.condvar.get(), self.mutex.get());
            debug_assert_eq!(r, 0);
        }
        let r = libc::pthread_mutex_unlock(self.mutex.get());
        debug_assert_eq!(r, 0);
    }

    // Parks the thread until it is unparked or the timeout is reached. This
    // should be called after it has been added to the queue, after unlocking
    // the queue. Returns true if we were unparked and false if we timed out.
    pub unsafe fn park_until(&self, timeout: Instant) -> bool {
        let r = libc::pthread_mutex_lock(self.mutex.get());
        debug_assert_eq!(r, 0);
        while self.should_park.get() {
            let now = Instant::now();
            if timeout <= now {
                let r = libc::pthread_mutex_unlock(self.mutex.get());
                debug_assert_eq!(r, 0);
                return false;
            }

            // Convert the timeout to a target system time
            let diff = timeout - now;
            let ts;
            match (SystemTime::now() + diff).duration_since(UNIX_EPOCH) {
                Ok(dur) => {
                    ts = libc::timespec {
                        tv_sec: dur.as_secs() as libc::time_t,
                        tv_nsec: dur.subsec_nanos() as libc::c_long,
                    };
                }
                Err(err) => {
                    // Handle times before the epoch in case the system clock is
                    // set to something strange...
                    let dur = err.duration();
                    if dur.subsec_nanos() != 0 {
                        ts = libc::timespec {
                            tv_sec: -(dur.as_secs() as libc::time_t + 1),
                            tv_nsec: 1000000000 - dur.subsec_nanos() as libc::c_long,
                        };
                    } else {
                        ts = libc::timespec {
                            tv_sec: -(dur.as_secs() as libc::time_t),
                            tv_nsec: 0,
                        };
                    }
                }
            }
            let r = libc::pthread_cond_timedwait(self.condvar.get(), self.mutex.get(), &ts);
            if ts.tv_sec < 0 {
                // On some systems, negative timeouts will return EINVAL
                debug_assert!(r == 0 || r == libc::ETIMEDOUT || r == libc::EINVAL);
            } else {
                debug_assert!(r == 0 || r == libc::ETIMEDOUT);
            }
        }
        let r = libc::pthread_mutex_unlock(self.mutex.get());
        debug_assert_eq!(r, 0);
        true
    }

    // Lock the parker to prevent the target thread from exiting. This is
    // necessary to ensure that thread-local ThreadData objects remain valid.
    // This should be called while holding the queue lock.
    pub unsafe fn unpark_lock(&self) -> () {
        let r = libc::pthread_mutex_lock(self.mutex.get());
        debug_assert_eq!(r, 0);
    }

    // Wakes up the parked thread. This should be called after the queue lock is
    // released to avoid blocking the queue for too long.
    pub unsafe fn unpark(&self, _lock: ()) {
        self.should_park.set(false);

        // We notify while holding the lock here to avoid races with the target
        // thread. In particular, the thread could exit after we unlock the
        // mutex, which would make the condvar access invalid memory.
        let r = libc::pthread_cond_signal(self.condvar.get());
        debug_assert_eq!(r, 0);
        let r = libc::pthread_mutex_unlock(self.mutex.get());
        debug_assert_eq!(r, 0);
    }
}

impl Drop for ThreadParker {
    fn drop(&mut self) {
        // On DragonFly pthread_mutex_destroy() returns EINVAL if called on a
        // mutex that was just initialized with libc::PTHREAD_MUTEX_INITIALIZER.
        // Once it is used (locked/unlocked) or pthread_mutex_init() is called,
        // this behaviour no longer occurs. The same applies to condvars.
        unsafe {
            let r = libc::pthread_mutex_destroy(self.mutex.get());
            if cfg!(target_os = "dragonfly") {
                debug_assert!(r == 0 || r == libc::EINVAL);
            } else {
                debug_assert_eq!(r, 0);
            }
            let r = libc::pthread_cond_destroy(self.condvar.get());
            if cfg!(target_os = "dragonfly") {
                debug_assert!(r == 0 || r == libc::EINVAL);
            } else {
                debug_assert_eq!(r, 0);
            }
        }
    }
}
