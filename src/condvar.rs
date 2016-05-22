// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use std::sync::atomic::{AtomicPtr, Ordering};
use std::time::{Duration, Instant};
use std::ptr;
use parking_lot::{self, UnparkResult, RequeueOp};
use mutex::{MutexGuard, guard_lock};
use raw_mutex::RawMutex;
use poison::{Poison, LockResult};

/// A type indicating whether a timed wait on a condition variable returned
/// due to a time out or not.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub struct WaitTimeoutResult(bool);

impl WaitTimeoutResult {
    /// Returns whether the wait was known to have timed out.
    #[inline]
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
/// Note that this module places one additional restriction over the system
/// condition variables: each condvar can be used with only one mutex at a
/// time. Any attempt to use multiple mutexes on the same condition variable
/// simultaneously will result in a runtime panic. However it is possible to
/// switch to a different mutex if there are no threads currently waiting on
/// the condition variable.
///
/// # Differences from the standard library `Condvar`
///
/// - No spurious wakeups: A wait will only return a non-timeout result if it
///   was woken up by `notify_one` or `notify_all`.
/// - Only requires 1 word of space, whereas the standard library boxes the
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
///     let mut started = lock.lock().unwrap();
///     *started = true;
///     cvar.notify_one();
/// });
///
/// // wait for the thread to start up
/// let &(ref lock, ref cvar) = &*pair;
/// let mut started = lock.lock().unwrap();
/// while !*started {
///     started = cvar.wait(started).unwrap();
/// }
/// ```
pub struct Condvar {
    state: AtomicPtr<RawMutex>,
}

impl Condvar {
    /// Creates a new condition variable which is ready to be waited on and
    /// notified.
    #[cfg(feature = "nightly")]
    #[inline]
    pub const fn new() -> Condvar {
        Condvar { state: AtomicPtr::new(ptr::null_mut()) }
    }

    /// Creates a new condition variable which is ready to be waited on and
    /// notified.
    #[cfg(not(feature = "nightly"))]
    #[inline]
    pub fn new() -> Condvar {
        Condvar { state: AtomicPtr::new(ptr::null_mut()) }
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
        if self.state.load(Ordering::Relaxed).is_null() {
            return;
        }

        self.notify_one_slow();
    }

    #[cold]
    #[inline(never)]
    fn notify_one_slow(&self) {
        unsafe {
            // Unpark one thread
            let addr = self as *const _ as usize;
            let callback = &mut |result| {
                // Clear our state if there are no more waiting threads
                if result != UnparkResult::UnparkedNotLast {
                    self.state.store(ptr::null_mut(), Ordering::Relaxed);
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
        if self.state.load(Ordering::Relaxed).is_null() {
            return;
        }

        self.notify_all_slow();
    }

    #[cold]
    #[inline(never)]
    fn notify_all_slow(&self) {
        unsafe {
            // Unpark one thread and requeue the rest onto the mutex
            let mutex = self.state.load(Ordering::Relaxed);
            let from = self as *const _ as usize;
            let to = mutex as usize;
            let validate = &mut || {
                // Make sure that our atomic state still points to the same
                // mutex. If not then it means that all threads on the current
                // mutex were woken up and a new waiting thread switched to a
                // different mutex. In that case we can get away with doing
                // nothing.
                if self.state.load(Ordering::Relaxed) != mutex {
                    return RequeueOp::Abort;
                }

                // Clear our state since we are going to unpark or requeue all
                // threads.
                self.state.store(ptr::null_mut(), Ordering::Relaxed);

                // Unpark one thread if the mutex is unlocked, otherwise just
                // requeue everything to the mutex. This is safe to do here
                // since unlocking the mutex when the parked bit is set requires
                // locking the queue. There is the possibility of a race if the
                // mutex gets locked after we check, but that doesn't matter in
                // this case.
                if (*mutex).mark_parked_if_locked() {
                    RequeueOp::RequeueAll
                } else {
                    RequeueOp::UnparkOneRequeueRest
                }
            };
            let callback = &mut |op, num_threads| {
                // If we requeued threads to the mutex, mark it as having
                // parked threads. The RequeueAll case is already handled above.
                if op == RequeueOp::UnparkOneRequeueRest && num_threads > 1 {
                    (*mutex).mark_parked();
                }
            };
            parking_lot::unpark_requeue(from, to, validate, callback);
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
    ///
    /// # Errors
    ///
    /// This function will return an error if the mutex being waited on is
    /// poisoned when this thread re-acquires the lock. For more information,
    /// see information about poisoning on the Mutex type.
    ///
    /// # Panics
    ///
    /// This function will panic if another thread is waiting on the `Condvar`
    /// with a different `Mutex` object.
    #[inline]
    pub fn wait<'a, T: ?Sized>(&self,
                               mutex_guard: MutexGuard<'a, T>)
                               -> LockResult<MutexGuard<'a, T>> {
        self.wait_internal(guard_lock(&mutex_guard)).map_lock_result(mutex_guard)
    }

    // This is a non-generic function to reduce the monomorphization cost of
    // using `wait`.
    fn wait_internal(&self, mutex: &RawMutex) -> Poison {
        unsafe {
            let mut bad_mutex = false;
            {
                let addr = self as *const _ as usize;
                let lock_addr = mutex as *const _ as *mut _;
                let validate = &mut || {
                    // Ensure we don't use two different mutexes with the same
                    // Condvar at the same time.
                    let state = self.state.load(Ordering::Relaxed);
                    if !state.is_null() && state != lock_addr {
                        bad_mutex = true;
                        return false;
                    }

                    // This is done while locked to avoid races with notify_one
                    self.state.store(lock_addr, Ordering::Relaxed);
                    true
                };
                let before_sleep = &mut || {
                    // Unlock the mutex before sleeping...
                    mutex.unlock(Poison(false));
                };
                let timed_out = &mut |_, _| unreachable!();
                parking_lot::park(addr, validate, before_sleep, timed_out, None);
            }

            // Panic if we tried to use multiple mutexes with a Condvar. Note
            // that at this point the MutexGuard is still locked. It will be
            // unlocked by the unwinding logic.
            if bad_mutex {
                panic!("attempted to use a condition variable with more than one mutex");
            }

            // ... and re-lock it once we are done sleeping
            mutex.lock()
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
    ///
    /// # Errors
    ///
    /// This function will return an error if the mutex being waited on is
    /// poisoned when this thread re-acquires the lock. For more information,
    /// see information about poisoning on the Mutex type.
    ///
    /// # Panics
    ///
    /// This function will panic if another thread is waiting on the `Condvar`
    /// with a different `Mutex` object.
    pub fn wait_until<'a, T: ?Sized>(&self,
                                     mutex_guard: MutexGuard<'a, T>,
                                     timeout: Instant)
                                     -> LockResult<(MutexGuard<'a, T>, WaitTimeoutResult)> {
        let (poison, timeout) = self.wait_until_internal(guard_lock(&mutex_guard), timeout);
        poison.map_lock_result((mutex_guard, timeout))
    }

    // This is a non-generic function to reduce the monomorphization cost of
    // using `wait_until`.
    fn wait_until_internal(&self,
                           mutex: &RawMutex,
                           timeout: Instant)
                           -> (Poison, WaitTimeoutResult) {
        unsafe {
            let result;
            let mut bad_mutex = false;
            let mut requeued = false;
            if timeout <= Instant::now() {
                // If the timeout is in the past, we still need to release and
                // re-acquire the mutex.
                mutex.unlock(Poison(false));
                result = false;
            } else {
                let addr = self as *const _ as usize;
                let lock_addr = mutex as *const _ as *mut _;
                let validate = &mut || {
                    // Ensure we don't use two different mutexes with the same
                    // Condvar at the same time.
                    let state = self.state.load(Ordering::Relaxed);
                    if !state.is_null() && state != lock_addr {
                        bad_mutex = true;
                        return false;
                    }

                    // This is done while locked to avoid races with notify_one
                    self.state.store(lock_addr, Ordering::Relaxed);
                    true
                };
                let before_sleep = &mut || {
                    // Unlock the mutex before sleeping...
                    mutex.unlock(Poison(false));
                };
                let timed_out = &mut |k, r| {
                    // If we were requeued to a mutex, then we did not time out.
                    // We'll just park ourselves on the mutex again when we try
                    // to lock it later.
                    requeued = k != addr;

                    // If we were the last thread on the queue then we need to
                    // clear our state. This is normally done by the
                    // notify_{one,all} functions when not timing out.
                    if !requeued && r == UnparkResult::UnparkedLast {
                        self.state.store(ptr::null_mut(), Ordering::Relaxed);
                    }
                };
                result = parking_lot::park(addr, validate, before_sleep, timed_out, Some(timeout));
            }

            // Panic if we tried to use multiple mutexes with a Condvar. Note
            // that at this point the MutexGuard is still locked. It will be
            // unlocked by the unwinding logic.
            if bad_mutex {
                panic!("attempted to use a condition variable with more than one mutex");
            }

            // ... and re-lock it once we are done sleeping
            (mutex.lock(), WaitTimeoutResult(!(result || requeued)))
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
    pub fn wait_for<'a, T: ?Sized>(&self,
                                   guard: MutexGuard<'a, T>,
                                   timeout: Duration)
                                   -> LockResult<(MutexGuard<'a, T>, WaitTimeoutResult)> {
        self.wait_until(guard, Instant::now() + timeout)
    }
}

impl Default for Condvar {
    #[inline]
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

        let g = M.lock().unwrap();
        let _t = thread::spawn(move || {
            let _g = M.lock().unwrap();
            C.notify_one();
        });
        let g = C.wait(g).unwrap();
        drop(g);
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
                let mut cnt = lock.lock().unwrap();
                *cnt += 1;
                if *cnt == N {
                    tx.send(()).unwrap();
                }
                while *cnt != 0 {
                    cnt = cond.wait(cnt).unwrap();
                }
                tx.send(()).unwrap();
            });
        }
        drop(tx);

        let &(ref lock, ref cond) = &*data;
        rx.recv().unwrap();
        let mut cnt = lock.lock().unwrap();
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

        let g = M.lock().unwrap();
        let (g, no_timeout) = C.wait_for(g, Duration::from_millis(1)).unwrap();
        assert!(no_timeout.timed_out());
        let _t = thread::spawn(move || {
            let _g = M.lock().unwrap();
            C.notify_one();
        });
        let (g, timeout_res) = C.wait_for(g, Duration::from_millis(u32::max_value() as u64))
            .unwrap();
        assert!(!timeout_res.timed_out());
        drop(g);
    }

    #[test]
    fn wait_until() {
        lazy_static! {
            static ref C: Condvar = Condvar::new();
            static ref M: Mutex<()> = Mutex::new(());
        }

        let g = M.lock().unwrap();
        let (g, no_timeout) = C.wait_until(g, Instant::now() + Duration::from_millis(1)).unwrap();
        assert!(no_timeout.timed_out());
        let _t = thread::spawn(move || {
            let _g = M.lock().unwrap();
            C.notify_one();
        });
        let (g, timeout_res) = C.wait_until(g,
                        Instant::now() + Duration::from_millis(u32::max_value() as u64))
            .unwrap();
        assert!(!timeout_res.timed_out());
        drop(g);
    }

    #[test]
    #[should_panic]
    fn two_mutexes() {
        lazy_static! {
            static ref C: Condvar = Condvar::new();
            static ref M1: Mutex<()> = Mutex::new(());
            static ref M2: Mutex<()> = Mutex::new(());
        }

        // Make sure we don't leave the child thread dangling
        struct PanicGuard;
        impl Drop for PanicGuard {
            fn drop(&mut self) {
                C.notify_one();
            }
        }

        let (tx, rx) = channel();
        let g = M1.lock().unwrap();
        let _t = thread::spawn(move || {
            let g = M1.lock().unwrap();
            tx.send(()).unwrap();
            let _ = C.wait(g).unwrap();
        });
        drop(g);
        rx.recv().unwrap();
        let _g = M1.lock().unwrap();
        let _guard = PanicGuard;
        let _ = C.wait(M2.lock().unwrap()).unwrap();
    }

    #[test]
    fn two_mutexes_disjoint() {
        lazy_static! {
            static ref C: Condvar = Condvar::new();
            static ref M1: Mutex<()> = Mutex::new(());
            static ref M2: Mutex<()> = Mutex::new(());
        }

        let mut g = M1.lock().unwrap();
        let _t = thread::spawn(move || {
            let _g = M1.lock().unwrap();
            C.notify_one();
        });
        g = C.wait(g).unwrap();
        drop(g);

        let _ = C.wait_for(M2.lock().unwrap(), Duration::from_millis(1)).unwrap();
    }
}
