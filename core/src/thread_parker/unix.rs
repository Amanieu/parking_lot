// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use super::libstd::{
    thread,
    time::{Duration, Instant},
};
#[cfg(any(target_os = "macos", target_os = "ios"))]
use core::ptr;
use core::{
    cell::{Cell, UnsafeCell},
    mem,
};
use libc;

// x32 Linux uses a non-standard type for tv_nsec in timespec.
// See https://sourceware.org/bugzilla/show_bug.cgi?id=16437
#[cfg(all(target_arch = "x86_64", target_pointer_width = "32"))]
#[allow(non_camel_case_types)]
type tv_nsec_t = i64;
#[cfg(not(all(target_arch = "x86_64", target_pointer_width = "32")))]
#[allow(non_camel_case_types)]
type tv_nsec_t = libc::c_long;

// Helper type for putting a thread to sleep until some other thread wakes it up
pub struct ThreadParker {
    should_park: Cell<bool>,
    mutex: UnsafeCell<libc::pthread_mutex_t>,
    condvar: UnsafeCell<libc::pthread_cond_t>,
    initialized: Cell<bool>,
}

impl ThreadParker {
    pub const IS_CHEAP_TO_CONSTRUCT: bool = false;

    #[inline]
    pub fn new() -> ThreadParker {
        ThreadParker {
            should_park: Cell::new(false),
            mutex: UnsafeCell::new(libc::PTHREAD_MUTEX_INITIALIZER),
            condvar: UnsafeCell::new(libc::PTHREAD_COND_INITIALIZER),
            initialized: Cell::new(false),
        }
    }

    // Initializes the condvar to use CLOCK_MONOTONIC instead of CLOCK_REALTIME.
    #[cfg(any(target_os = "macos", target_os = "ios", target_os = "android"))]
    #[inline]
    unsafe fn init(&self) {}
    #[cfg(not(any(target_os = "macos", target_os = "ios", target_os = "android")))]
    #[inline]
    unsafe fn init(&self) {
        let mut attr: libc::pthread_condattr_t = mem::uninitialized();
        let r = libc::pthread_condattr_init(&mut attr);
        debug_assert_eq!(r, 0);
        let r = libc::pthread_condattr_setclock(&mut attr, libc::CLOCK_MONOTONIC);
        debug_assert_eq!(r, 0);
        let r = libc::pthread_cond_init(self.condvar.get(), &attr);
        debug_assert_eq!(r, 0);
        let r = libc::pthread_condattr_destroy(&mut attr);
        debug_assert_eq!(r, 0);
    }

    // Prepares the parker. This should be called before adding it to the queue.
    #[inline]
    pub unsafe fn prepare_park(&self) {
        self.should_park.set(true);
        if !self.initialized.get() {
            self.init();
            self.initialized.set(true);
        }
    }

    // Checks if the park timed out. This should be called while holding the
    // queue lock after park_until has returned false.
    #[inline]
    pub unsafe fn timed_out(&self) -> bool {
        // We need to grab the mutex here because another thread may be
        // concurrently executing UnparkHandle::unpark, which is done without
        // holding the queue lock.
        let r = libc::pthread_mutex_lock(self.mutex.get());
        debug_assert_eq!(r, 0);
        let should_park = self.should_park.get();
        let r = libc::pthread_mutex_unlock(self.mutex.get());
        debug_assert_eq!(r, 0);
        should_park
    }

    // Parks the thread until it is unparked. This should be called after it has
    // been added to the queue, after unlocking the queue.
    #[inline]
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
    #[inline]
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

            if let Some(ts) = timeout_to_timespec(timeout - now) {
                let r = libc::pthread_cond_timedwait(self.condvar.get(), self.mutex.get(), &ts);
                if ts.tv_sec < 0 {
                    // On some systems, negative timeouts will return EINVAL. In
                    // that case we won't sleep and will just busy loop instead,
                    // which is the best we can do.
                    debug_assert!(r == 0 || r == libc::ETIMEDOUT || r == libc::EINVAL);
                } else {
                    debug_assert!(r == 0 || r == libc::ETIMEDOUT);
                }
            } else {
                // Timeout calculation overflowed, just sleep indefinitely
                let r = libc::pthread_cond_wait(self.condvar.get(), self.mutex.get());
                debug_assert_eq!(r, 0);
            }
        }
        let r = libc::pthread_mutex_unlock(self.mutex.get());
        debug_assert_eq!(r, 0);
        true
    }

    // Locks the parker to prevent the target thread from exiting. This is
    // necessary to ensure that thread-local ThreadData objects remain valid.
    // This should be called while holding the queue lock.
    #[inline]
    pub unsafe fn unpark_lock(&self) -> UnparkHandle {
        let r = libc::pthread_mutex_lock(self.mutex.get());
        debug_assert_eq!(r, 0);

        UnparkHandle {
            thread_parker: self,
        }
    }
}

impl Drop for ThreadParker {
    #[inline]
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
        let r = libc::pthread_cond_signal((*self.thread_parker).condvar.get());
        debug_assert_eq!(r, 0);
        let r = libc::pthread_mutex_unlock((*self.thread_parker).mutex.get());
        debug_assert_eq!(r, 0);
    }
}

// Returns the current time on the clock used by pthread_cond_t as a timespec.
#[cfg(any(target_os = "macos", target_os = "ios"))]
#[inline]
fn timespec_now() -> libc::timespec {
    let mut now: libc::timeval = unsafe { mem::uninitialized() };
    let r = unsafe { libc::gettimeofday(&mut now, ptr::null_mut()) };
    debug_assert_eq!(r, 0);
    libc::timespec {
        tv_sec: now.tv_sec,
        tv_nsec: now.tv_usec as tv_nsec_t * 1000,
    }
}
#[cfg(not(any(target_os = "macos", target_os = "ios")))]
#[inline]
fn timespec_now() -> libc::timespec {
    let mut now: libc::timespec = unsafe { mem::uninitialized() };
    let clock = if cfg!(target_os = "android") {
        // Android doesn't support pthread_condattr_setclock, so we need to
        // specify the timeout in CLOCK_REALTIME.
        libc::CLOCK_REALTIME
    } else {
        libc::CLOCK_MONOTONIC
    };
    let r = unsafe { libc::clock_gettime(clock, &mut now) };
    debug_assert_eq!(r, 0);
    now
}

// Converts a relative timeout into an absolute timeout in the clock used by
// pthread_cond_t.
#[inline]
fn timeout_to_timespec(timeout: Duration) -> Option<libc::timespec> {
    // Handle overflows early on
    if timeout.as_secs() > libc::time_t::max_value() as u64 {
        return None;
    }

    let now = timespec_now();
    let mut nsec = now.tv_nsec + timeout.subsec_nanos() as tv_nsec_t;
    let mut sec = now.tv_sec.checked_add(timeout.as_secs() as libc::time_t);
    if nsec >= 1_000_000_000 {
        nsec -= 1_000_000_000;
        sec = sec.and_then(|sec| sec.checked_add(1));
    }

    sec.map(|sec| libc::timespec {
        tv_nsec: nsec,
        tv_sec: sec,
    })
}

#[inline]
pub fn thread_yield() {
    thread::yield_now();
}
