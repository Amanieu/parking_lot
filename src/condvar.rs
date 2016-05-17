// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};
use parking_lot::{self, UnparkResult};
use mutex::{MutexGuard, guard_lock};

/// A type indicating whether a timed wait on a condition variable returned
/// due to a time out or not.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub struct WaitTimeoutResult(bool);

impl WaitTimeoutResult {
    /// Returns whether the wait was known to have timed out.
    pub fn timed_out(&self) -> bool {
        self.0
    }
}

/// A Condition Variable
///
/// Condition variables represent the ability to block a thread such that it
/// consumes no CPU time while waiting for an event to occur. Condition
/// variables are typically associated with a boolean predicate (a condition)
/// and a mutex. The predicate is always verified inside of the mutex before
/// determining that thread must block.
///
/// # Differences from the standard library `Condvar`
///
/// - No spurious wakeups: A wait will only return a non-timeout result if it
///   was woken up by `notify_one` or `notify_all`.
/// - Only requires 1 byte of space, whereas the standard library boxes the
///   `Condvar` due to platform limitations.
/// - Can be statically constructed (requires the `const_fn` nightly feature).
/// - Does not require any drop glue when dropped.
/// - Inline fast path for the uncontended case.
///
/// # Examples
///
/// ```
/// use parking_lot::{Mutex, Condvar};
/// use std::sync::Arc;
/// use std::thread;
///
/// let pair = Arc::new((Mutex::new(false), Condvar::new()));
/// let pair2 = pair.clone();
///
/// // Inside of our lock, spawn a new thread, and then wait for it to start
/// thread::spawn(move|| {
///     let &(ref lock, ref cvar) = &*pair2;
///     let mut started = lock.lock();
///     *started = true;
///     cvar.notify_one();
/// });
///
/// // wait for the thread to start up
/// let &(ref lock, ref cvar) = &*pair;
/// let mut started = lock.lock();
/// while !*started {
///     cvar.wait(&mut started);
/// }
/// ```
pub struct Condvar {
    state: AtomicBool,
}

impl Condvar {
    /// Creates a new condition variable which is ready to be waited on and
    /// notified.
    #[cfg(feature = "nightly")]
    #[inline]
    pub const fn new() -> Condvar {
        Condvar { state: AtomicBool::new(false) }
    }

    /// Creates a new condition variable which is ready to be waited on and
    /// notified.
    #[cfg(not(feature = "nightly"))]
    #[inline]
    pub fn new() -> Condvar {
        Condvar { state: AtomicBool::new(false) }
    }

    /// Wakes up one blocked thread on this condvar.
    ///
    /// If there is a blocked thread on this condition variable, then it will
    /// be woken up from its call to `wait` or `wait_timeout`. Calls to
    /// `notify_one` are not buffered in any way.
    ///
    /// To wake up all threads, see `notify_all()`.
    #[inline]
    pub fn notify_one(&self) {
        // Nothing to do if there are no waiting threads
        if !self.state.load(Ordering::Relaxed) {
            return;
        }

        unsafe {
            // Unpark one thread
            let addr = self as *const _ as usize;
            let callback = &mut |result| {
                // Clear our state if there are no more waiting threads
                if result != UnparkResult::UnparkedNotLast {
                    self.state.store(false, Ordering::Relaxed);
                }
            };
            parking_lot::unpark_one(addr, callback);
        }
    }

    /// Wakes up all blocked threads on this condvar.
    ///
    /// This method will ensure that any current waiters on the condition
    /// variable are awoken. Calls to `notify_all()` are not buffered in any
    /// way.
    ///
    /// To wake up only one thread, see `notify_one()`.
    #[inline]
    pub fn notify_all(&self) {
        // Nothing to do if there are no waiting threads
        if !self.state.load(Ordering::Relaxed) {
            return;
        }

        // Clear our state since we are going to wake all threads up anyways
        self.state.store(false, Ordering::Relaxed);

        unsafe {
            // Unpark all threads
            let addr = self as *const _ as usize;
            parking_lot::unpark_all(addr);
        }
    }

    /// Blocks the current thread until this condition variable receives a
    /// notification.
    ///
    /// This function will atomically unlock the mutex specified (represented by
    /// `mutex_guard`) and block the current thread. This means that any calls
    /// to `notify_*()` which happen logically after the mutex is unlocked are
    /// candidates to wake this thread up. When this function call returns, the
    /// lock specified will have been re-acquired.
    #[inline]
    pub fn wait<T: ?Sized>(&self, guard: &mut MutexGuard<T>) {
        unsafe {
            let addr = self as *const _ as usize;
            let validate = &mut || {
                // This is done while locked to avoid races with notify_one
                self.state.store(true, Ordering::Relaxed);
                true
            };
            let before_sleep = &mut || {
                // Unlock the mutex before sleeping...
                guard_lock(guard).unlock();
            };
            parking_lot::park(addr, validate, before_sleep, None);

            // ... and re-lock it once we are done sleeping
            guard_lock(guard).lock();
        }
    }

    /// Waits on this condition variable for a notification, timing out after
    /// the specified time instant.
    ///
    /// The semantics of this function are equivalent to `wait()` except that
    /// the thread will be blocked roughly until `timeout` is reached. This
    /// method should not be used for precise timing due to anomalies such as
    /// preemption or platform differences that may not cause the maximum
    /// amount of time waited to be precisely `timeout`.
    ///
    /// The returned `WaitTimeoutResult` value indicates if the timeout is
    /// known to have elapsed.
    ///
    /// Like `wait`, the lock specified will be re-acquired when this function
    /// returns, regardless of whether the timeout elapsed or not.
    #[inline]
    pub fn wait_until<T: ?Sized>(&self,
                                 guard: &mut MutexGuard<T>,
                                 timeout: Instant)
                                 -> WaitTimeoutResult {
        unsafe {
            let result;
            if timeout <= Instant::now() {
                // If the timeout is in the past, we still need to release and
                // re-acquire the mutex.
                guard_lock(guard).unlock();
                result = false;
            } else {
                let addr = self as *const _ as usize;
                let validate = &mut || {
                    // This is done while locked to avoid races with notify_one
                    self.state.store(true, Ordering::Relaxed);
                    true
                };
                let before_sleep = &mut || {
                    // Unlock the mutex before sleeping...
                    guard_lock(guard).unlock();
                };
                result = parking_lot::park(addr, validate, before_sleep, Some(timeout));
            }

            // ... and re-lock it once we are done sleeping
            guard_lock(guard).lock();

            WaitTimeoutResult(!result)
        }
    }

    /// Waits on this condition variable for a notification, timing out after a
    /// specified duration.
    ///
    /// The semantics of this function are equivalent to `wait()` except that
    /// the thread will be blocked for roughly no longer than `timeout`. This
    /// method should not be used for precise timing due to anomalies such as
    /// preemption or platform differences that may not cause the maximum
    /// amount of time waited to be precisely `timeout`.
    ///
    /// The returned `WaitTimeoutResult` value indicates if the timeout is
    /// known to have elapsed.
    ///
    /// Like `wait`, the lock specified will be re-acquired when this function
    /// returns, regardless of whether the timeout elapsed or not.
    #[inline]
    pub fn wait_for<T: ?Sized>(&self,
                               guard: &mut MutexGuard<T>,
                               timeout: Duration)
                               -> WaitTimeoutResult {
        self.wait_until(guard, Instant::now() + timeout)
    }
}

impl Default for Condvar {
    fn default() -> Condvar {
        Condvar::new()
    }
}

#[cfg(test)]
mod tests {
    use std::sync::mpsc::channel;
    use std::sync::Arc;
    use std::thread;
    use std::time::{Duration, Instant};
    use {Condvar, Mutex};

    #[test]
    fn smoke() {
        let c = Condvar::new();
        c.notify_one();
        c.notify_all();
    }

    #[test]
    fn notify_one() {
        lazy_static! {
            static ref C: Condvar = Condvar::new();
            static ref M: Mutex<()> = Mutex::new(());
        }

        let mut g = M.lock();
        let _t = thread::spawn(move || {
            let _g = M.lock();
            C.notify_one();
        });
        C.wait(&mut g);
    }

    #[test]
    fn notify_all() {
        const N: usize = 10;

        let data = Arc::new((Mutex::new(0), Condvar::new()));
        let (tx, rx) = channel();
        for _ in 0..N {
            let data = data.clone();
            let tx = tx.clone();
            thread::spawn(move || {
                let &(ref lock, ref cond) = &*data;
                let mut cnt = lock.lock();
                *cnt += 1;
                if *cnt == N {
                    tx.send(()).unwrap();
                }
                while *cnt != 0 {
                    cond.wait(&mut cnt);
                }
                tx.send(()).unwrap();
            });
        }
        drop(tx);

        let &(ref lock, ref cond) = &*data;
        rx.recv().unwrap();
        let mut cnt = lock.lock();
        *cnt = 0;
        cond.notify_all();
        drop(cnt);

        for _ in 0..N {
            rx.recv().unwrap();
        }
    }

    #[test]
    fn wait_for() {
        lazy_static! {
            static ref C: Condvar = Condvar::new();
            static ref M: Mutex<()> = Mutex::new(());
        }

        let mut g = M.lock();
        let no_timeout = C.wait_for(&mut g, Duration::from_millis(1));
        assert!(no_timeout.timed_out());
        let _t = thread::spawn(move || {
            let _g = M.lock();
            C.notify_one();
        });
        let timeout_res = C.wait_for(&mut g, Duration::from_millis(u32::max_value() as u64));
        assert!(!timeout_res.timed_out());
        drop(g);
    }

    #[test]
    fn wait_until() {
        lazy_static! {
            static ref C: Condvar = Condvar::new();
            static ref M: Mutex<()> = Mutex::new(());
        }

        let mut g = M.lock();
        let no_timeout = C.wait_until(&mut g, Instant::now() + Duration::from_millis(1));
        assert!(no_timeout.timed_out());
        let _t = thread::spawn(move || {
            let _g = M.lock();
            C.notify_one();
        });
        let timeout_res = C.wait_until(&mut g,
                                       Instant::now() +
                                       Duration::from_millis(u32::max_value() as u64));
        assert!(!timeout_res.timed_out());
        drop(g);
    }
}
