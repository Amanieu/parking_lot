// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::mutex::{MutexGuard, RawMutex, RawMutexTimed};
use core::{fmt, ops::DerefMut};

/// Provides the inner implementation for a [`Condvar`] over a particular
/// type of [`RawMutex`].
///
/// # Safety
///
/// Implementions must ensure that [`wait`] is safe to call, regardless of the
/// specific [`RawMutex`] instance provided. If an implementation only supports
/// one instance at a time, [`wait`] may panic.
///
/// [`wait`]: RawCondvar::wait
pub unsafe trait RawCondvar {
    /// Initial value for a new condvar.
    // A “non-constant” const item is a legacy way to supply an initialized value to downstream
    // static items. Can hopefully be replaced with `const fn new() -> Self` at some point.
    #[allow(clippy::declare_interior_mutable_const)]
    const INIT: Self;

    /// The type of [`RawMutex`] this condvar can work with.
    type RawMutex: RawMutex;

    /// Wait until the provided [`RawMutex`] is available.
    ///
    /// # Safety
    ///
    /// Caller must ensure the provided `mutex` is locked, and that they are the
    /// owner of said lock for the duration of this call.
    ///
    /// # Panics
    ///
    /// Implementations are permitted to panic if requested to wait on two distinct
    /// [`RawMutex`]s simultaneously.
    unsafe fn wait(&self, mutex: &Self::RawMutex);

    /// Notify a single waiting thread.
    fn notify_one(&self) -> bool;

    /// Notify all waiting threads.
    fn notify_all(&self) -> usize;
}

/// Additional methods for [`RawCondvar`] which support timeouts.
///
/// # Safety
///
/// Implementions must ensure that [`wait_for`] and [`wait_until`] are safe to call,
/// regardless of the specific [`RawMutex`] instance provided. If an implementation
/// only supports one instance at a time, waiting may panic.
///
/// [`wait_for`]: RawCondvar::wait_for
/// [`wait_until`]: RawCondvar::wait_until
pub unsafe trait RawCondvarTimed: RawCondvar
where
    Self::RawMutex: RawMutexTimed,
{
    /// Attmped to convert the provided [`Duration`](RawMutexTimed::Duration) into
    /// an [`Instant`](RawMutexTimed::Instant). Returns [`None`] if the provided
    /// duration is further into the future than can be represented by an instant.
    fn checked_duration_to_instant(
        timeout: &<Self::RawMutex as RawMutexTimed>::Duration,
    ) -> Option<<Self::RawMutex as RawMutexTimed>::Instant>;

    /// Wait until the provided [`RawMutex`] is available until the provided
    /// timeout is reached.
    ///
    /// # Safety
    ///
    /// Caller must ensure the provided `mutex` is locked, and that they are the
    /// owner of said lock for the duration of this call.
    ///
    /// # Panics
    ///
    /// Implementations are permitted to panic if requested to wait on two distinct
    /// [`RawMutex`]s simultaneously.
    unsafe fn wait_until(
        &self,
        mutex: &Self::RawMutex,
        timeout: &<Self::RawMutex as RawMutexTimed>::Instant,
    ) -> bool;

    /// Wait until the provided [`RawMutex`] is available until the provided
    /// timeout is reached.
    ///
    /// # Safety
    ///
    /// Caller must ensure the provided `mutex` is locked, and that they are the
    /// owner of said lock for the duration of this call.
    ///
    /// # Panics
    ///
    /// Implementations are permitted to panic if requested to wait on two distinct
    /// [`RawMutex`]s simultaneously.
    unsafe fn wait_for(
        &self,
        mutex: &Self::RawMutex,
        timeout: &<Self::RawMutex as RawMutexTimed>::Duration,
    ) -> bool {
        // SAFETY: `RawCondvar::wait` and `RawCondvarTimed::wait_until` have the
        // same safety condition as this function, which is assured by the caller.
        unsafe {
            match Self::checked_duration_to_instant(timeout) {
                Some(timeout) => self.wait_until(mutex, &timeout),
                None => {
                    // No absolute deadline can be constructed, so fall back to
                    // an untimed wait.
                    <Self as RawCondvar>::wait(self, mutex);
                    false
                }
            }
        }
    }
}

/// A type indicating whether a timed wait on a condition variable timed out.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub struct WaitTimeoutResult(bool);

impl WaitTimeoutResult {
    /// Returns `true` if the wait was known to have timed out.
    #[inline]
    pub const fn timed_out(self) -> bool {
        self.0
    }
}

/// A condition variable.
///
/// Condition variables represent the ability to block a thread such that it
/// consumes no CPU time while waiting for an event to occur. Condition
/// variables are typically associated with a boolean predicate (a condition)
/// and a mutex. The predicate is always verified inside of the mutex before
/// determining that thread must block.
pub struct Condvar<C> {
    inner: C,
}

impl<C: RawCondvar> Condvar<C> {
    /// Creates a new condition variable which is ready to be waited on and
    /// notified.
    #[inline]
    pub const fn new() -> Condvar<C> {
        Condvar { inner: C::INIT }
    }

    /// Returns the underlying raw condvar object.
    ///
    /// Note that you will most likely need to import the `RawCondvar` trait from
    /// `lock_api` to be able to call functions on the raw condvar.
    #[inline]
    pub fn raw(&self) -> &C {
        &self.inner
    }

    /// Wakes up one blocked thread on this condvar.
    ///
    /// Returns whether a thread was woken up.
    ///
    /// If there is a blocked thread on this condition variable, then it will
    /// be woken up from its call to `wait` or `wait_timeout`.
    ///
    /// To wake up all threads, see `notify_all()`.
    #[inline]
    pub fn notify_one(&self) -> bool {
        self.inner.notify_one()
    }

    /// Wakes up all blocked threads on this condvar.
    ///
    /// Returns the number of threads woken up.
    ///
    /// This method will ensure that any current waiters on the condition
    /// variable are awoken.
    ///
    /// To wake up only one thread, see `notify_one()`.
    #[inline]
    pub fn notify_all(&self) -> usize {
        self.inner.notify_all()
    }

    /// Blocks the current thread until this condition variable receives a
    /// notification.
    ///
    /// This function will unlock the mutex specified (represented by
    /// `mutex_guard`) and block the current thread. This means that any calls
    /// to `notify_*()` which happen logically after the mutex is unlocked are
    /// candidates to wake this thread up. When this function call returns, the
    /// lock specified will have been re-acquired.
    ///
    /// # Panics
    ///
    /// The underlying [`RawCondvar`] implementation provided by `C` is permitted
    /// to panic if requested to wait on two distinct [`MutexGuard`]s simultaneously.
    #[inline]
    pub fn wait<T: ?Sized>(&self, mutex_guard: &mut MutexGuard<'_, C::RawMutex, T>) {
        unsafe {
            self.inner.wait(MutexGuard::mutex(mutex_guard).raw());
        }
    }

    /// Blocks the current thread until this condition variable receives a
    /// notification. If the provided condition evaluates to `false`, then the
    /// thread is no longer blocked and the operation is completed. If the
    /// condition evaluates to `true`, then the thread is blocked again and
    /// waits for another notification before repeating this process.
    ///
    /// This function will unlock the mutex specified (represented by
    /// `mutex_guard`) and block the current thread. This means that any calls
    /// to `notify_*()` which happen logically after the mutex is unlocked are
    /// candidates to wake this thread up. When this function call returns, the
    /// lock specified will have been re-acquired.
    ///
    /// # Panics
    ///
    /// The underlying [`RawCondvar`] implementation provided by `C` is permitted
    /// to panic if requested to wait on two distinct [`MutexGuard`]s simultaneously.
    #[inline]
    pub fn wait_while<T, F>(
        &self,
        mutex_guard: &mut MutexGuard<'_, C::RawMutex, T>,
        mut condition: F,
    ) where
        T: ?Sized,
        F: FnMut(&mut T) -> bool,
    {
        while condition(mutex_guard.deref_mut()) {
            unsafe {
                self.inner.wait(MutexGuard::mutex(mutex_guard).raw());
            }
        }
    }
}

impl<R: RawMutexTimed, C: RawCondvarTimed<RawMutex = R>> Condvar<C> {
    /// Waits on this condition variable for a notification, timing out after
    /// the specified time instant.
    ///
    /// The semantics of this function are equivalent to `wait()` except that
    /// the thread will be blocked roughly until `timeout` is reached. This
    /// method should not be used for precise timing due to anomalies such as
    /// preemption or platform differences that may not cause the maximum
    /// amount of time waited to be precisely `timeout`.
    ///
    /// Note that the best effort is made to ensure that the time waited is
    /// measured with a monotonic clock, and not affected by the changes made to
    /// the system time.
    ///
    /// The returned [`WaitTimeoutResult`] indicates whether the wait ended
    /// because the timeout elapsed rather than because of a notification.
    ///
    /// Like `wait`, the lock specified will be re-acquired when this function
    /// returns, regardless of whether the timeout elapsed or not.
    ///
    /// # Panics
    ///
    /// The underlying [`RawCondvar`] implementation provided by `C` is permitted
    /// to panic if requested to wait on two distinct [`MutexGuard`]s simultaneously.
    #[inline]
    pub fn wait_until<T: ?Sized>(
        &self,
        mutex_guard: &mut MutexGuard<'_, C::RawMutex, T>,
        timeout: <C::RawMutex as RawMutexTimed>::Instant,
    ) -> WaitTimeoutResult {
        WaitTimeoutResult(unsafe {
            self.inner
                .wait_until(MutexGuard::mutex(mutex_guard).raw(), &timeout)
        })
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
    /// Note that the best effort is made to ensure that the time waited is
    /// measured with a monotonic clock, and not affected by the changes made to
    /// the system time.
    ///
    /// The returned [`WaitTimeoutResult`] indicates whether the wait ended
    /// because the timeout elapsed rather than because of a notification.
    ///
    /// Like `wait`, the lock specified will be re-acquired when this function
    /// returns, regardless of whether the timeout elapsed or not.
    ///
    /// # Panics
    ///
    /// The underlying [`RawCondvar`] implementation provided by `C` is permitted
    /// to panic if requested to wait on two distinct [`MutexGuard`]s simultaneously.
    #[inline]
    pub fn wait_for<T: ?Sized>(
        &self,
        mutex_guard: &mut MutexGuard<'_, C::RawMutex, T>,
        timeout: <C::RawMutex as RawMutexTimed>::Duration,
    ) -> WaitTimeoutResult {
        WaitTimeoutResult(unsafe {
            self.inner
                .wait_for(MutexGuard::mutex(mutex_guard).raw(), &timeout)
        })
    }

    /// Waits on this condition variable for a notification, timing out after
    /// the specified time instant. If the provided condition evaluates to
    /// `false`, then the thread is no longer blocked and the operation is
    /// completed. If the condition evaluates to `true`, then the thread is
    /// blocked again and waits for another notification before repeating
    /// this process.
    ///
    /// The semantics of this function are equivalent to `wait()` except that
    /// the thread will be blocked roughly until `timeout` is reached. This
    /// method should not be used for precise timing due to anomalies such as
    /// preemption or platform differences that may not cause the maximum
    /// amount of time waited to be precisely `timeout`.
    ///
    /// Note that the best effort is made to ensure that the time waited is
    /// measured with a monotonic clock, and not affected by the changes made to
    /// the system time.
    ///
    /// The returned [`WaitTimeoutResult`] indicates whether the wait timed out
    /// while the condition remained `true`.
    ///
    /// Like `wait`, the lock specified will be re-acquired when this function
    /// returns, regardless of whether the timeout elapsed or not.
    ///
    /// # Panics
    ///
    /// The underlying [`RawCondvar`] implementation provided by `C` is permitted
    /// to panic if requested to wait on two distinct [`MutexGuard`]s simultaneously.
    #[inline]
    pub fn wait_while_until<T, F>(
        &self,
        mutex_guard: &mut MutexGuard<'_, C::RawMutex, T>,
        mut condition: F,
        timeout: <C::RawMutex as RawMutexTimed>::Instant,
    ) -> WaitTimeoutResult
    where
        T: ?Sized,
        F: FnMut(&mut T) -> bool,
    {
        let mut result = WaitTimeoutResult(false);

        loop {
            if !condition(mutex_guard.deref_mut()) {
                return WaitTimeoutResult(false);
            }
            if result.timed_out() {
                return result;
            }
            result = WaitTimeoutResult(unsafe {
                self.inner
                    .wait_until(MutexGuard::mutex(mutex_guard).raw(), &timeout)
            });
        }
    }

    /// Waits on this condition variable for a notification, timing out after a
    /// specified duration. If the provided condition evaluates to `false`,
    /// then the thread is no longer blocked and the operation is completed.
    /// If the condition evaluates to `true`, then the thread is blocked again
    /// and waits for another notification before repeating this process.
    ///
    /// The semantics of this function are equivalent to `wait()` except that
    /// the thread will be blocked for roughly no longer than `timeout`. This
    /// method should not be used for precise timing due to anomalies such as
    /// preemption or platform differences that may not cause the maximum
    /// amount of time waited to be precisely `timeout`.
    ///
    /// Note that the best effort is made to ensure that the time waited is
    /// measured with a monotonic clock, and not affected by the changes made to
    /// the system time.
    ///
    /// The returned [`WaitTimeoutResult`] indicates whether the wait timed out
    /// while the condition remained `true`.
    ///
    /// Like `wait`, the lock specified will be re-acquired when this function
    /// returns, regardless of whether the timeout elapsed or not.
    ///
    /// # Panics
    ///
    /// The underlying [`RawCondvar`] implementation provided by `C` is permitted
    /// to panic if requested to wait on two distinct [`MutexGuard`]s simultaneously.
    #[inline]
    pub fn wait_while_for<T: ?Sized, F>(
        &self,
        mutex_guard: &mut MutexGuard<'_, C::RawMutex, T>,
        condition: F,
        timeout: <C::RawMutex as RawMutexTimed>::Duration,
    ) -> WaitTimeoutResult
    where
        F: FnMut(&mut T) -> bool,
    {
        match C::checked_duration_to_instant(&timeout) {
            Some(timeout) => self.wait_while_until(mutex_guard, condition, timeout),
            None => {
                // No absolute deadline can be constructed, so fall back to an
                // untimed wait.
                self.wait_while(mutex_guard, condition);
                WaitTimeoutResult(false)
            }
        }
    }
}

impl<C: RawCondvar> Default for Condvar<C> {
    #[inline]
    fn default() -> Condvar<C> {
        Condvar::new()
    }
}

impl<C> fmt::Debug for Condvar<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad("Condvar { .. }")
    }
}
