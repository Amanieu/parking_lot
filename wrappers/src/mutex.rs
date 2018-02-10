// Copyright 2018 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use core::cell::UnsafeCell;
use core::ops::{Deref, DerefMut};
use core::fmt;
use core::mem;
use core::marker::PhantomData;

#[cfg(feature = "owning_ref")]
use owning_ref::StableAddress;

/// Basic operations for a mutex.
///
/// Types implementing this trait can be used by `Mutex` to form a safe and
/// fully-functioning mutex type.
///
/// # Safety
///
/// Implementations of this trait must ensure that the mutex is actually
/// exclusive: a lock can't be acquired while the mutex is already locked.
pub unsafe trait RawMutex {
    /// Initial value for an unlocked mutex.
    const INIT: Self;

    /// Acquires this mutex, blocking the current thread until it is able to do so.
    fn lock(&self);

    /// Attempts to acquire this mutex without blocking.
    fn try_lock(&self) -> bool;

    /// Unlocks this mutex.
    fn unlock(&self);
}

/// Additional methods for mutexes which support fair unlocking.
///
/// Fair unlocking means that a lock is handed directly over to the next waiting
/// thread if there is one, without giving other threads the opportunity to
/// "steal" the lock in the meantime. This is typically slower than unfair
/// unlocking, but may be necessary in certain circumstances.
pub unsafe trait RawMutexFair: RawMutex {
    /// Unlocks this mutex using a fair unlock protocol.
    fn unlock_fair(&self);

    /// Temporarily yields the mutex to a waiting thread if there is one.
    ///
    /// This method is functionally equivalent to calling `unlock_fair` followed
    /// by `lock`, however it can be much more efficient in the case where there
    /// are no waiting threads.
    fn bump(&self) {
        self.unlock_fair();
        self.lock();
    }
}

/// Additional methods for mutexes which support locking with timeouts.
///
/// The `Duration` and `Instant` types are specified as associated types so that
/// this trait is usable even in `no_std` environments.
pub unsafe trait RawMutexTimed: RawMutex {
    /// Duration type used for `try_lock_for`.
    type Duration;

    /// Instant type used for `try_lock_until`.
    type Instant;

    /// Attempts to acquire this lock until a timeout is reached.
    fn try_lock_for(&self, timeout: Self::Duration) -> bool;

    /// Attempts to acquire this lock until a timeout is reached.
    fn try_lock_until(&self, timeout: Self::Instant) -> bool;
}

/// A mutual exclusion primitive useful for protecting shared data
///
/// This mutex will block threads waiting for the lock to become available. The
/// mutex can also be statically initialized or created via a `new`
/// constructor. Each mutex has a type parameter which represents the data that
/// it is protecting. The data can only be accessed through the RAII guards
/// returned from `lock` and `try_lock`, which guarantees that the data is only
/// ever accessed when the mutex is locked.
pub struct Mutex<R: RawMutex, T: ?Sized> {
    raw: R,
    data: UnsafeCell<T>,
}

unsafe impl<R: RawMutex + Send, T: ?Sized + Send> Send for Mutex<R, T> {}
unsafe impl<R: RawMutex + Sync, T: ?Sized + Send> Sync for Mutex<R, T> {}

/// An RAII implementation of a "scoped lock" of a mutex. When this structure is
/// dropped (falls out of scope), the lock will be unlocked.
///
/// The data protected by the mutex can be accessed through this guard via its
/// `Deref` and `DerefMut` implementations.
#[must_use]
pub struct MutexGuard<'a, R: RawMutex + 'a, T: ?Sized + 'a> {
    raw: &'a R,
    data: *mut T,
    marker: PhantomData<&'a mut T>,
}

unsafe impl<'a, R: RawMutex + Sync + 'a, T: ?Sized + Sync + 'a> Sync for MutexGuard<'a, R, T> {}

impl<R: RawMutex, T> Mutex<R, T> {
    /// Creates a new mutex in an unlocked state ready for use.
    #[cfg(feature = "nightly")]
    #[inline]
    pub const fn new(val: T) -> Mutex<R, T> {
        Mutex {
            data: UnsafeCell::new(val),
            raw: R::INIT,
        }
    }

    /// Creates a new mutex in an unlocked state ready for use.
    #[cfg(not(feature = "nightly"))]
    #[inline]
    pub fn new(val: T) -> Mutex<R, T> {
        Mutex {
            data: UnsafeCell::new(val),
            raw: R::INIT,
        }
    }

    /// Consumes this mutex, returning the underlying data.
    #[inline]
    #[allow(unused_unsafe)]
    pub fn into_inner(self) -> T {
        unsafe { self.data.into_inner() }
    }
}

impl<R: RawMutex, T: ?Sized> Mutex<R, T> {
    #[inline]
    fn guard(&self) -> MutexGuard<R, T> {
        MutexGuard {
            raw: &self.raw,
            data: self.data.get(),
            marker: PhantomData,
        }
    }

    /// Acquires a mutex, blocking the current thread until it is able to do so.
    ///
    /// This function will block the local thread until it is available to acquire
    /// the mutex. Upon returning, the thread is the only thread with the mutex
    /// held. An RAII guard is returned to allow scoped unlock of the lock. When
    /// the guard goes out of scope, the mutex will be unlocked.
    ///
    /// Attempts to lock a mutex in the thread which already holds the lock will
    /// result in a deadlock.
    #[inline]
    pub fn lock(&self) -> MutexGuard<R, T> {
        self.raw.lock();
        self.guard()
    }

    /// Attempts to acquire this lock.
    ///
    /// If the lock could not be acquired at this time, then `None` is returned.
    /// Otherwise, an RAII guard is returned. The lock will be unlocked when the
    /// guard is dropped.
    ///
    /// This function does not block.
    #[inline]
    pub fn try_lock(&self) -> Option<MutexGuard<R, T>> {
        if self.raw.try_lock() {
            Some(self.guard())
        } else {
            None
        }
    }

    /// Returns a mutable reference to the underlying data.
    ///
    /// Since this call borrows the `Mutex` mutably, no actual locking needs to
    /// take place---the mutable borrow statically guarantees no locks exist.
    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        unsafe { &mut *self.data.get() }
    }

    /// Returns the underlying raw mutex object.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it allows unlocking a mutex while
    /// still holding a reference to a `MutexGuard`.
    pub unsafe fn raw(&self) -> &R {
        &self.raw
    }
}

impl<R: RawMutexTimed, T: ?Sized> Mutex<R, T> {
    /// Attempts to acquire this lock until a timeout is reached.
    ///
    /// If the lock could not be acquired before the timeout expired, then
    /// `None` is returned. Otherwise, an RAII guard is returned. The lock will
    /// be unlocked when the guard is dropped.
    #[inline]
    pub fn try_lock_for(&self, timeout: R::Duration) -> Option<MutexGuard<R, T>> {
        if self.raw.try_lock_for(timeout) {
            Some(self.guard())
        } else {
            None
        }
    }

    /// Attempts to acquire this lock until a timeout is reached.
    ///
    /// If the lock could not be acquired before the timeout expired, then
    /// `None` is returned. Otherwise, an RAII guard is returned. The lock will
    /// be unlocked when the guard is dropped.
    #[inline]
    pub fn try_lock_until(&self, timeout: R::Instant) -> Option<MutexGuard<R, T>> {
        if self.raw.try_lock_until(timeout) {
            Some(self.guard())
        } else {
            None
        }
    }
}

impl<R: RawMutex, T: ?Sized + Default> Default for Mutex<R, T> {
    #[inline]
    fn default() -> Mutex<R, T> {
        Mutex::new(Default::default())
    }
}

impl<R: RawMutex, T> From<T> for Mutex<R, T> {
    #[inline]
    fn from(t: T) -> Mutex<R, T> {
        Mutex::new(t)
    }
}

impl<R: RawMutex, T: ?Sized + fmt::Debug> fmt::Debug for Mutex<R, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.try_lock() {
            Some(guard) => f.debug_struct("Mutex")
                .field("data", &&*guard)
                .finish(),
            None => f.pad("Mutex { <locked> }"),
        }
    }
}

impl<'a, R: RawMutex + 'a, T: ?Sized + 'a> MutexGuard<'a, R, T> {
    /// Returns the underlying raw mutex object.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it allows unlocking a mutex while
    /// still holding a reference to a `MutexGuard`.
    pub unsafe fn raw(s: &Self) -> &R {
        s.raw
    }

    /// Makes a new `MutexGuard` for a component of the locked data.
    ///
    /// This operation cannot fail as the `MutexGuard` passed
    /// in already locked the mutex.
    ///
    /// This is an associated function that needs to be
    /// used as `MutexGuard::map(...)`. A method would interfere with methods of
    /// the same name on the contents of the locked data.
    #[inline]
    pub fn map<U: ?Sized, F>(s: Self, f: F) -> MutexGuard<'a, R, U>
    where
        F: FnOnce(&mut T) -> &mut U,
    {
        let raw = s.raw;
        let data = f(unsafe { &mut *s.data });
        mem::forget(s);
        MutexGuard {
            raw,
            data,
            marker: PhantomData,
        }
    }

    /// Executes the given function with the mutex unlocked.
    ///
    /// This is safe because `&mut` guarantees that there exist no other
    /// references to the data protected by the mutex.
    #[inline]
    pub fn unlocked<F, U>(s: &mut Self, f: F) -> U
    where
        F: FnOnce() -> U,
    {
        s.raw.unlock();
        defer!(s.raw.lock());
        f()
    }
}

impl<'a, R: RawMutexFair + 'a, T: ?Sized + 'a> MutexGuard<'a, R, T> {
    /// Unlocks the mutex using a fair unlock protocol.
    ///
    /// By default, mutexes are unfair and allow the current thread to re-lock
    /// the mutex before another has the chance to acquire the lock, even if
    /// that thread has been blocked on the mutex for a long time. This is the
    /// default because it allows much higher throughput as it avoids forcing a
    /// context switch on every mutex unlock. This can result in one thread
    /// acquiring a mutex many more times than other threads.
    ///
    /// However in some cases it can be beneficial to ensure fairness by forcing
    /// the lock to pass on to a waiting thread if there is one. This is done by
    /// using this method instead of dropping the `MutexGuard` normally.
    #[inline]
    pub fn unlock_fair(s: Self) {
        s.raw.unlock_fair();
        mem::forget(s);
    }

    /// Executes the given function with the mutex unlocked using a fair unlock
    /// protocol.
    ///
    /// This is safe because `&mut` guarantees that there exist no other
    /// references to the data protected by the mutex.
    #[inline]
    pub fn unlocked_fair<F, U>(s: &mut Self, f: F) -> U
    where
        F: FnOnce() -> U,
    {
        s.raw.unlock_fair();
        defer!(s.raw.lock());
        f()
    }

    /// Temporarily yields the mutex to a waiting thread if there is one.
    ///
    /// This method is functionally equivalent to calling `unlock_fair` followed
    /// by `lock`, however it can be much more efficient in the case where there
    /// are no waiting threads.
    #[inline]
    pub fn bump(s: &mut Self) {
        s.raw.bump();
    }
}

impl<'a, R: RawMutex + 'a, T: ?Sized + 'a> Deref for MutexGuard<'a, R, T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        unsafe { &*self.data }
    }
}

impl<'a, R: RawMutex + 'a, T: ?Sized + 'a> DerefMut for MutexGuard<'a, R, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.data }
    }
}

impl<'a, R: RawMutex + 'a, T: ?Sized + 'a> Drop for MutexGuard<'a, R, T> {
    #[inline]
    fn drop(&mut self) {
        self.raw.unlock();
    }
}

#[cfg(feature = "owning_ref")]
unsafe impl<'a, R: RawMutex + 'a, T: ?Sized + 'a> StableAddress for MutexGuard<'a, R, T> {}
