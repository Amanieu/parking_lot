use core::cell::UnsafeCell;
use core::fmt;
use core::marker::PhantomData;
use core::mem;
use core::ops::{Deref, DerefMut};
use scopeguard::defer;

use crate::guard::{ExclusiveGuardData, abort_on_panic};

#[cfg(feature = "arc_lock")]
use alloc::sync::Arc;
#[cfg(feature = "arc_lock")]
use core::mem::ManuallyDrop;
#[cfg(feature = "arc_lock")]
use core::ptr;

#[cfg(feature = "owning_ref")]
use owning_ref::StableAddress;

#[cfg(feature = "serde")]
use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// Basic operations for a mutex.
///
/// Types implementing this trait can be used by `Mutex` to form a safe and
/// fully-functioning mutex type.
///
/// # Safety
///
/// Implementations must enforce mutual exclusion: after a locking operation
/// successfully acquires the mutex, no other locking operation may succeed
/// until the mutex is unlocked.
///
/// Successful lock acquisitions must have acquire semantics, and unlocking
/// operations must have release semantics. These requirements also apply to
/// equivalent operations provided by subtraits.
///
/// Methods which acquire the mutex may unwind, but if they do then the current
/// context must not acquire the mutex. Methods which release or temporarily
/// yield the mutex must not unwind.
pub unsafe trait RawMutex {
    /// Initial value for an unlocked mutex.
    // A “non-constant” const item is a legacy way to supply an initialized value to downstream
    // static items. Can hopefully be replaced with `const fn new() -> Self` at some point.
    #[allow(clippy::declare_interior_mutable_const)]
    const INIT: Self;

    /// Marker type which determines whether a lock guard should be [`Send`].
    /// Use [`GuardSend`](crate::GuardSend) or [`GuardNoSend`](crate::GuardNoSend).
    type GuardMarker;

    /// Acquires this mutex, blocking the current thread until it is able to do so.
    fn lock(&self);

    /// Attempts to acquire this mutex without blocking. Returns `true`
    /// if the lock was successfully acquired and `false` otherwise.
    fn try_lock(&self) -> bool;

    /// Unlocks this mutex.
    ///
    /// # Safety
    ///
    /// This method may only be called if the mutex is held in the current context, i.e. it must
    /// be paired with a successful call to [`lock`], [`try_lock`], [`try_lock_for`] or [`try_lock_until`].
    ///
    /// [`lock`]: RawMutex::lock
    /// [`try_lock`]: RawMutex::try_lock
    /// [`try_lock_for`]: RawMutexTimed::try_lock_for
    /// [`try_lock_until`]: RawMutexTimed::try_lock_until
    unsafe fn unlock(&self);

    /// Checks whether the mutex is currently locked.
    ///
    /// The result is a momentary snapshot and may be stale by the time it is
    /// returned.
    fn is_locked(&self) -> bool;
}

/// Additional methods for mutexes which support fair unlocking.
///
/// Fair unlocking means that a lock is handed directly over to the next waiting
/// thread if there is one, without giving other threads the opportunity to
/// "steal" the lock in the meantime. This is typically slower than unfair
/// unlocking, but may be necessary in certain circumstances.
///
/// # Safety
///
/// Implementations must uphold the safety requirements of [`RawMutex`] for
/// the additional methods provided by this trait.
pub unsafe trait RawMutexFair: RawMutex {
    /// Unlocks this mutex using a fair unlock protocol.
    ///
    /// # Safety
    ///
    /// This method may only be called if the mutex is held in the current context, see
    /// the documentation of [`unlock`](RawMutex::unlock).
    unsafe fn unlock_fair(&self);

    /// Temporarily yields the mutex to a waiting thread if there is one.
    ///
    /// This method is functionally equivalent to calling `unlock_fair` followed
    /// by `lock`, however it can be much more efficient in the case where there
    /// are no waiting threads.
    ///
    /// # Safety
    ///
    /// This method may only be called if the mutex is held in the current context, see
    /// the documentation of [`unlock`](RawMutex::unlock).
    ///
    /// # Aborts
    ///
    /// The default implementation aborts if re-locking the mutex panics.
    unsafe fn bump(&self) {
        unsafe { self.unlock_fair() };
        abort_on_panic(|| self.lock());
    }
}

/// Additional methods for mutexes which support locking with timeouts.
///
/// The `Duration` and `Instant` types are specified as associated types so that
/// this trait is usable even in `no_std` environments.
///
/// # Safety
///
/// Implementations must uphold the safety requirements of [`RawMutex`] for
/// the additional methods provided by this trait.
pub unsafe trait RawMutexTimed: RawMutex {
    /// Duration type used for `try_lock_for`.
    type Duration;

    /// Instant type used for `try_lock_until`.
    type Instant;

    /// Attempts to acquire this lock until a timeout is reached.
    ///
    /// A successful operation may return early. An unsuccessful operation must
    /// not return before the timeout, but may return later due to scheduling or
    /// platform-specific behavior.
    fn try_lock_for(&self, timeout: Self::Duration) -> bool;

    /// Attempts to acquire this lock until a timeout is reached.
    ///
    /// A successful operation may return early. An unsuccessful operation must
    /// not return before the timeout, but may return later due to scheduling or
    /// platform-specific behavior.
    fn try_lock_until(&self, timeout: Self::Instant) -> bool;
}

/// A mutual exclusion primitive useful for protecting shared data.
///
/// This mutex will block threads waiting for the lock to become available. The
/// mutex can also be statically initialized or created via a `new`
/// constructor. Each mutex has a type parameter which represents the data that
/// it is protecting. The data can only be accessed through the RAII guards
/// returned from `lock` and `try_lock`, which guarantees that the data is only
/// ever accessed when the mutex is locked.
pub struct Mutex<R, T: ?Sized> {
    raw: R,
    data: UnsafeCell<T>,
}

unsafe impl<R: RawMutex + Sync, T: ?Sized + Send> Sync for Mutex<R, T> {}

impl<R: RawMutex, T> Mutex<R, T> {
    /// Creates a new mutex in an unlocked state ready for use.
    #[inline]
    pub const fn new(val: T) -> Mutex<R, T> {
        Mutex {
            raw: R::INIT,
            data: UnsafeCell::new(val),
        }
    }

    /// Consumes this mutex, returning the underlying data.
    #[inline]
    pub fn into_inner(self) -> T {
        self.data.into_inner()
    }
}

impl<R, T> Mutex<R, T> {
    /// Creates a new mutex based on a pre-existing raw mutex.
    #[inline]
    pub const fn from_raw(raw_mutex: R, val: T) -> Mutex<R, T> {
        Mutex {
            raw: raw_mutex,
            data: UnsafeCell::new(val),
        }
    }

    /// Consumes this mutex, returning the underlying data and raw mutex.
    #[inline]
    pub fn into_inner_with_raw(self) -> (R, T) {
        (self.raw, self.data.into_inner())
    }
}

impl<R: RawMutex, T: ?Sized> Mutex<R, T> {
    /// Creates a new `MutexGuard` without checking if the mutex is locked.
    ///
    /// # Safety
    ///
    /// This method must only be called if the thread logically holds the lock.
    ///
    /// Calling this function when a guard has already been produced is undefined behavior unless
    /// the guard was forgotten with `mem::forget`.
    #[inline]
    pub unsafe fn make_guard_unchecked(&self) -> MutexGuard<'_, R, T> {
        MutexGuard {
            mutex: self,
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
    /// The exact behavior when the current thread tries to acquire a mutex it
    /// already holds is left unspecified. The second call will not return; it
    /// may panic or deadlock, for example.
    ///
    /// # Panics
    ///
    /// This function may panic if the lock is already held by the current
    /// thread.
    #[inline]
    #[track_caller]
    pub fn lock(&self) -> MutexGuard<'_, R, T> {
        self.raw.lock();
        // SAFETY: The lock is held, as required.
        unsafe { self.make_guard_unchecked() }
    }

    /// Attempts to acquire this lock.
    ///
    /// If the lock could not be acquired at this time, then `None` is returned.
    /// Otherwise, an RAII guard is returned. The lock will be unlocked when the
    /// guard is dropped.
    ///
    /// This function does not block.
    #[inline]
    #[track_caller]
    pub fn try_lock(&self) -> Option<MutexGuard<'_, R, T>> {
        if self.raw.try_lock() {
            // SAFETY: The lock is held, as required.
            Some(unsafe { self.make_guard_unchecked() })
        } else {
            None
        }
    }

    /// Returns a mutable reference to the underlying data.
    ///
    /// Since this call borrows the `Mutex` mutably, no actual locking needs to
    /// take place -- the mutable borrow statically guarantees no new locks can
    /// be acquired while the reference exists. This method does not clear a
    /// lock previously abandoned by forgetting a [`MutexGuard`].
    #[inline]
    pub const fn get_mut(&mut self) -> &mut T {
        self.data.get_mut()
    }

    /// Checks whether the mutex is currently locked.
    ///
    /// The result is a momentary snapshot and may be stale by the time it is
    /// returned.
    #[inline]
    #[track_caller]
    pub fn is_locked(&self) -> bool {
        self.raw.is_locked()
    }

    /// Forcibly unlocks the mutex.
    ///
    /// This is useful when combined with `mem::forget` to hold a lock without
    /// the need to maintain a `MutexGuard` object alive, for example when
    /// dealing with FFI.
    ///
    /// # Safety
    ///
    /// This method must only be called if the current thread logically owns a
    /// `MutexGuard` but that guard has been discarded using `mem::forget`.
    /// Behavior is undefined if a mutex is unlocked when not locked.
    #[inline]
    #[track_caller]
    pub unsafe fn force_unlock(&self) {
        unsafe { self.raw.unlock() };
    }

    /// Returns the underlying raw mutex object.
    ///
    /// Note that you will most likely need to import the `RawMutex` trait from
    /// `lock_api` to be able to call functions on the raw mutex.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it allows unlocking a mutex while
    /// still holding a reference to a `MutexGuard`.
    #[inline]
    pub unsafe fn raw(&self) -> &R {
        &self.raw
    }

    /// Returns a raw pointer to the underlying data.
    ///
    /// The returned pointer is always non-null and properly aligned, but the
    /// caller must ensure that reads and writes through it are properly
    /// synchronized and that the pointer is not used after the mutex is
    /// dropped.
    #[inline]
    pub const fn data_ptr(&self) -> *mut T {
        self.data.get()
    }

    /// Creates a new `ArcMutexGuard` without checking if the mutex is locked.
    ///
    /// # Safety
    ///
    /// This method must only be called if the thread logically holds the lock.
    ///
    /// Calling this function when a guard has already been produced is undefined behavior unless
    /// the guard was forgotten with `mem::forget`.
    #[cfg(feature = "arc_lock")]
    #[inline]
    unsafe fn make_arc_guard_unchecked(self: &Arc<Self>) -> ArcMutexGuard<R, T> {
        ArcMutexGuard {
            mutex: self.clone(),
            data_marker: PhantomData,
            marker: PhantomData,
        }
    }

    /// Acquires a lock through an `Arc`.
    ///
    /// This method is similar to the `lock` method; however, it requires the `Mutex` to be inside of an `Arc`
    /// and the resulting mutex guard owns a clone of the `Arc` instead of borrowing the lock.
    #[cfg(feature = "arc_lock")]
    #[inline]
    #[track_caller]
    pub fn lock_arc(self: &Arc<Self>) -> ArcMutexGuard<R, T> {
        self.raw.lock();
        // SAFETY: the locking guarantee is upheld
        unsafe { self.make_arc_guard_unchecked() }
    }

    /// Attempts to acquire a lock through an `Arc`.
    ///
    /// This method is similar to the `try_lock` method; however, it requires the `Mutex` to be inside of an
    /// `Arc` and the resulting mutex guard owns a clone of the `Arc` instead of borrowing the lock.
    #[cfg(feature = "arc_lock")]
    #[inline]
    #[track_caller]
    pub fn try_lock_arc(self: &Arc<Self>) -> Option<ArcMutexGuard<R, T>> {
        if self.raw.try_lock() {
            // SAFETY: locking guarantee is upheld
            Some(unsafe { self.make_arc_guard_unchecked() })
        } else {
            None
        }
    }
}

impl<R: RawMutexFair, T: ?Sized> Mutex<R, T> {
    /// Forcibly unlocks the mutex using a fair unlock protocol.
    ///
    /// This is useful when combined with `mem::forget` to hold a lock without
    /// the need to maintain a `MutexGuard` object alive, for example when
    /// dealing with FFI.
    ///
    /// # Safety
    ///
    /// This method must only be called if the current thread logically owns a
    /// `MutexGuard` but that guard has been discarded using `mem::forget`.
    /// Behavior is undefined if a mutex is unlocked when not locked.
    #[inline]
    #[track_caller]
    pub unsafe fn force_unlock_fair(&self) {
        unsafe { self.raw.unlock_fair() };
    }
}

impl<R: RawMutexTimed, T: ?Sized> Mutex<R, T> {
    /// Attempts to acquire this lock until a timeout is reached.
    ///
    /// If the lock could not be acquired before the timeout expired, then
    /// `None` is returned. Otherwise, an RAII guard is returned. The lock will
    /// be unlocked when the guard is dropped.
    ///
    /// A successful operation may return early. An unsuccessful operation will
    /// not return before the timeout, but may return later due to scheduling or
    /// platform-specific behavior.
    #[inline]
    #[track_caller]
    pub fn try_lock_for(&self, timeout: R::Duration) -> Option<MutexGuard<'_, R, T>> {
        if self.raw.try_lock_for(timeout) {
            // SAFETY: The lock is held, as required.
            Some(unsafe { self.make_guard_unchecked() })
        } else {
            None
        }
    }

    /// Attempts to acquire this lock until a timeout is reached.
    ///
    /// If the lock could not be acquired before the timeout expired, then
    /// `None` is returned. Otherwise, an RAII guard is returned. The lock will
    /// be unlocked when the guard is dropped.
    ///
    /// A successful operation may return early. An unsuccessful operation will
    /// not return before the timeout, but may return later due to scheduling or
    /// platform-specific behavior.
    #[inline]
    #[track_caller]
    pub fn try_lock_until(&self, timeout: R::Instant) -> Option<MutexGuard<'_, R, T>> {
        if self.raw.try_lock_until(timeout) {
            // SAFETY: The lock is held, as required.
            Some(unsafe { self.make_guard_unchecked() })
        } else {
            None
        }
    }

    /// Attempts to acquire this lock through an `Arc` until a timeout is reached.
    ///
    /// This method is similar to the `try_lock_for` method; however, it requires the `Mutex` to be inside of an
    /// `Arc` and the resulting mutex guard owns a clone of the `Arc` instead of borrowing the lock.
    ///
    /// See [`try_lock_for`](Self::try_lock_for) for timeout behavior.
    #[cfg(feature = "arc_lock")]
    #[inline]
    #[track_caller]
    pub fn try_lock_arc_for(self: &Arc<Self>, timeout: R::Duration) -> Option<ArcMutexGuard<R, T>> {
        if self.raw.try_lock_for(timeout) {
            // SAFETY: locking guarantee is upheld
            Some(unsafe { self.make_arc_guard_unchecked() })
        } else {
            None
        }
    }

    /// Attempts to acquire this lock through an `Arc` until a timeout is reached.
    ///
    /// This method is similar to the `try_lock_until` method; however, it requires the `Mutex` to be inside of
    /// an `Arc` and the resulting mutex guard owns a clone of the `Arc` instead of borrowing the lock.
    ///
    /// See [`try_lock_until`](Self::try_lock_until) for timeout behavior.
    #[cfg(feature = "arc_lock")]
    #[inline]
    #[track_caller]
    pub fn try_lock_arc_until(
        self: &Arc<Self>,
        timeout: R::Instant,
    ) -> Option<ArcMutexGuard<R, T>> {
        if self.raw.try_lock_until(timeout) {
            // SAFETY: locking guarantee is upheld
            Some(unsafe { self.make_arc_guard_unchecked() })
        } else {
            None
        }
    }
}

impl<R: RawMutex, T: Default> Default for Mutex<R, T> {
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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.try_lock() {
            Some(guard) => f.debug_struct("Mutex").field("data", &&*guard).finish(),
            None => {
                struct LockedPlaceholder;
                impl fmt::Debug for LockedPlaceholder {
                    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                        f.write_str("<locked>")
                    }
                }

                f.debug_struct("Mutex")
                    .field("data", &LockedPlaceholder)
                    .finish()
            }
        }
    }
}

// Copied and modified from serde
#[cfg(feature = "serde")]
impl<R, T> Serialize for Mutex<R, T>
where
    R: RawMutex,
    T: Serialize + ?Sized,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.lock().serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, R, T> Deserialize<'de> for Mutex<R, T>
where
    R: RawMutex,
    T: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Deserialize::deserialize(deserializer).map(Mutex::new)
    }
}

/// An RAII guard which unlocks the mutex when dropped.
///
/// The data protected by the mutex can be accessed through this guard via its
/// [`Deref`] and [`DerefMut`] implementations.
///
/// This structure is created by the [`lock`](Mutex::lock) and
/// [`try_lock`](Mutex::try_lock) methods on [`Mutex`].
#[clippy::has_significant_drop]
#[must_use = "if unused the Mutex will immediately unlock"]
pub struct MutexGuard<'a, R: RawMutex, T: ?Sized> {
    mutex: &'a Mutex<R, T>,
    marker: PhantomData<(&'a mut T, R::GuardMarker)>,
}

impl<'a, R: RawMutex + 'a, T: ?Sized + 'a> MutexGuard<'a, R, T> {
    /// Returns a reference to the original `Mutex` object.
    pub fn mutex(s: &Self) -> &'a Mutex<R, T> {
        s.mutex
    }

    /// Makes a new `MappedMutexGuard` for a component of the locked data.
    ///
    /// This is an associated function that needs to be
    /// used as `MutexGuard::map(...)`. A method would interfere with methods of
    /// the same name on the contents of the locked data.
    ///
    /// # Panics
    ///
    /// If `f` panics, the original guard is dropped.
    #[inline]
    pub fn map<U: ?Sized, F>(s: Self, f: F) -> MappedMutexGuard<'a, R, U>
    where
        F: FnOnce(&mut T) -> &mut U,
    {
        let raw = &s.mutex.raw;
        let data = f(unsafe { s.mutex.data.get().as_mut_unchecked() });
        mem::forget(s);
        MappedMutexGuard {
            raw,
            data: ExclusiveGuardData::new(data),
            marker: PhantomData,
        }
    }

    /// Attempts to make a new `MappedMutexGuard` for a component of the
    /// locked data. The original guard is returned if the closure returns `None`.
    ///
    /// This is an associated function that needs to be
    /// used as `MutexGuard::try_map(...)`. A method would interfere with methods of
    /// the same name on the contents of the locked data.
    ///
    /// # Panics
    ///
    /// If `f` panics, the original guard is dropped.
    #[inline]
    pub fn try_map<U: ?Sized, F>(s: Self, f: F) -> Result<MappedMutexGuard<'a, R, U>, Self>
    where
        F: FnOnce(&mut T) -> Option<&mut U>,
    {
        let raw = &s.mutex.raw;
        let Some(data) = f(unsafe { s.mutex.data.get().as_mut_unchecked() }) else {
            return Err(s);
        };
        mem::forget(s);
        Ok(MappedMutexGuard {
            raw,
            data: ExclusiveGuardData::new(data),
            marker: PhantomData,
        })
    }

    /// Attempts to make a new `MappedMutexGuard` for a component of the
    /// locked data. The original guard is returned alongside arbitrary user data
    /// if the closure returns `Err`.
    ///
    /// This is an associated function that needs to be
    /// used as `MutexGuard::try_map_or_err(...)`. A method would interfere with methods of
    /// the same name on the contents of the locked data.
    ///
    /// # Panics
    ///
    /// If `f` panics, the original guard is dropped.
    #[inline]
    pub fn try_map_or_err<U: ?Sized, F, E>(
        s: Self,
        f: F,
    ) -> Result<MappedMutexGuard<'a, R, U>, (Self, E)>
    where
        F: FnOnce(&mut T) -> Result<&mut U, E>,
    {
        let raw = &s.mutex.raw;
        let data = match f(unsafe { s.mutex.data.get().as_mut_unchecked() }) {
            Ok(data) => data,
            Err(e) => return Err((s, e)),
        };
        mem::forget(s);
        Ok(MappedMutexGuard {
            raw,
            data: ExclusiveGuardData::new(data),
            marker: PhantomData,
        })
    }

    /// Temporarily unlocks the mutex to execute the given function.
    ///
    /// This is safe because `&mut` guarantees that there exist no other
    /// references to the data protected by the mutex.
    ///
    /// # Aborts
    ///
    /// Aborts if re-locking the mutex panics.
    #[inline]
    #[track_caller]
    pub fn unlocked<F, U>(s: &mut Self, f: F) -> U
    where
        F: FnOnce() -> U,
    {
        // Safety: A MutexGuard always holds the lock.
        unsafe {
            s.mutex.raw.unlock();
        }
        defer!(abort_on_panic(|| s.mutex.raw.lock()));
        f()
    }

    /// Leaks the mutex guard and returns a mutable reference to the data
    /// protected by the mutex.
    ///
    /// This will leave the `Mutex` in a locked state.
    #[inline]
    pub fn leak(s: Self) -> &'a mut T {
        let r = unsafe { s.mutex.data.get().as_mut_unchecked() };
        mem::forget(s);
        r
    }
}

impl<'a, R: RawMutexFair + 'a, T: ?Sized + 'a> MutexGuard<'a, R, T> {
    /// Unlocks the mutex using a fair unlock protocol.
    ///
    /// A fair unlock hands the mutex directly to a waiting thread instead of
    /// allowing another thread to steal it. This can prevent starvation, but may
    /// reduce throughput by forcing a context switch.
    #[inline]
    #[track_caller]
    pub fn unlock_fair(s: Self) {
        // Safety: A MutexGuard always holds the lock.
        unsafe {
            s.mutex.raw.unlock_fair();
        }
        mem::forget(s);
    }

    /// Temporarily unlocks the mutex to execute the given function.
    ///
    /// The mutex is unlocked using a fair unlock protocol.
    ///
    /// This is safe because `&mut` guarantees that there exist no other
    /// references to the data protected by the mutex.
    ///
    /// # Aborts
    ///
    /// Aborts if re-locking the mutex panics.
    #[inline]
    #[track_caller]
    pub fn unlocked_fair<F, U>(s: &mut Self, f: F) -> U
    where
        F: FnOnce() -> U,
    {
        // Safety: A MutexGuard always holds the lock.
        unsafe {
            s.mutex.raw.unlock_fair();
        }
        defer!(abort_on_panic(|| s.mutex.raw.lock()));
        f()
    }

    /// Temporarily yields the mutex to a waiting thread if there is one.
    ///
    /// This method is functionally equivalent to calling `unlock_fair` followed
    /// by `lock`, however it can be much more efficient in the case where there
    /// are no waiting threads.
    #[inline]
    #[track_caller]
    pub fn bump(s: &mut Self) {
        // Safety: A MutexGuard always holds the lock.
        unsafe { s.mutex.raw.bump() };
    }
}

impl<'a, R: RawMutex + 'a, T: ?Sized + 'a> Deref for MutexGuard<'a, R, T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        unsafe { self.mutex.data.get().as_ref_unchecked() }
    }
}

impl<'a, R: RawMutex + 'a, T: ?Sized + 'a> DerefMut for MutexGuard<'a, R, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        unsafe { self.mutex.data.get().as_mut_unchecked() }
    }
}

impl<'a, R: RawMutex + 'a, T: ?Sized + 'a> Drop for MutexGuard<'a, R, T> {
    #[inline]
    fn drop(&mut self) {
        // Safety: A MutexGuard always holds the lock.
        unsafe {
            self.mutex.raw.unlock();
        }
    }
}

impl<'a, R: RawMutex + 'a, T: fmt::Debug + ?Sized + 'a> fmt::Debug for MutexGuard<'a, R, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<'a, R: RawMutex + 'a, T: fmt::Display + ?Sized + 'a> fmt::Display for MutexGuard<'a, R, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

#[cfg(feature = "owning_ref")]
unsafe impl<'a, R: RawMutex + 'a, T: ?Sized + 'a> StableAddress for MutexGuard<'a, R, T> {}

/// An RAII mutex guard returned by the `Arc` locking operations on [`Mutex`].
///
/// Unlike [`MutexGuard`], this guard owns the [`Arc`] used to unlock the mutex
/// instead of borrowing the mutex, so its lifetime is not tied to a lock
/// reference.
#[cfg(feature = "arc_lock")]
#[clippy::has_significant_drop]
#[must_use = "if unused the Mutex will immediately unlock"]
pub struct ArcMutexGuard<R: RawMutex, T: ?Sized> {
    mutex: Arc<Mutex<R, T>>,
    data_marker: PhantomData<T>,
    marker: PhantomData<R::GuardMarker>,
}

#[cfg(feature = "arc_lock")]
impl<R: RawMutex, T: ?Sized> ArcMutexGuard<R, T> {
    /// Returns a reference to the `Mutex` this is guarding, contained in its `Arc`.
    #[inline]
    pub fn mutex(s: &Self) -> &Arc<Mutex<R, T>> {
        &s.mutex
    }

    /// Unlocks the mutex and returns the `Arc` that was held by the [`ArcMutexGuard`].
    #[inline]
    #[track_caller]
    pub fn into_arc(s: Self) -> Arc<Mutex<R, T>> {
        // SAFETY: Skip our Drop impl and manually unlock the mutex.
        let s = ManuallyDrop::new(s);
        unsafe {
            s.mutex.raw.unlock();
            ptr::read(&s.mutex)
        }
    }

    /// Temporarily unlocks the mutex to execute the given function.
    ///
    /// This is safe because `&mut` guarantees that there exist no other
    /// references to the data protected by the mutex.
    ///
    /// # Aborts
    ///
    /// Aborts if re-locking the mutex panics.
    #[inline]
    #[track_caller]
    pub fn unlocked<F, U>(s: &mut Self, f: F) -> U
    where
        F: FnOnce() -> U,
    {
        // Safety: An ArcMutexGuard always holds the lock.
        unsafe {
            s.mutex.raw.unlock();
        }
        defer!(abort_on_panic(|| s.mutex.raw.lock()));
        f()
    }
}

#[cfg(feature = "arc_lock")]
impl<R: RawMutexFair, T: ?Sized> ArcMutexGuard<R, T> {
    /// Unlocks the mutex using a fair unlock protocol.
    ///
    /// This is functionally identical to the `unlock_fair` method on [`MutexGuard`].
    #[inline]
    #[track_caller]
    pub fn unlock_fair(s: Self) {
        drop(Self::into_arc_fair(s));
    }

    /// Unlocks the mutex using a fair unlock protocol and returns the `Arc` that was held by the [`ArcMutexGuard`].
    #[inline]
    pub fn into_arc_fair(s: Self) -> Arc<Mutex<R, T>> {
        // SAFETY: Skip our Drop impl and manually unlock the mutex.
        let s = ManuallyDrop::new(s);
        unsafe {
            s.mutex.raw.unlock_fair();
            ptr::read(&s.mutex)
        }
    }

    /// Temporarily unlocks the mutex to execute the given function.
    ///
    /// This is functionally identical to the `unlocked_fair` method on [`MutexGuard`].
    ///
    /// # Aborts
    ///
    /// Aborts if re-locking the mutex panics.
    #[inline]
    #[track_caller]
    pub fn unlocked_fair<F, U>(s: &mut Self, f: F) -> U
    where
        F: FnOnce() -> U,
    {
        // Safety: An ArcMutexGuard always holds the lock.
        unsafe {
            s.mutex.raw.unlock_fair();
        }
        defer!(abort_on_panic(|| s.mutex.raw.lock()));
        f()
    }

    /// Temporarily yields the mutex to a waiting thread if there is one.
    ///
    /// This is functionally identical to the `bump` method on [`MutexGuard`].
    #[inline]
    #[track_caller]
    pub fn bump(s: &mut Self) {
        // Safety: An ArcMutexGuard always holds the lock.
        unsafe { s.mutex.raw.bump() };
    }
}

#[cfg(feature = "arc_lock")]
impl<R: RawMutex, T: ?Sized> Deref for ArcMutexGuard<R, T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        unsafe { self.mutex.data.get().as_ref_unchecked() }
    }
}

#[cfg(feature = "arc_lock")]
impl<R: RawMutex, T: ?Sized> DerefMut for ArcMutexGuard<R, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        unsafe { self.mutex.data.get().as_mut_unchecked() }
    }
}

#[cfg(feature = "arc_lock")]
impl<R: RawMutex, T: ?Sized> Drop for ArcMutexGuard<R, T> {
    #[inline]
    fn drop(&mut self) {
        // Safety: An ArcMutexGuard always holds the lock.
        unsafe {
            self.mutex.raw.unlock();
        }
    }
}

/// An RAII mutex guard returned by [`MutexGuard::map`], which can point to a
/// subfield of the protected data.
///
/// The main difference between `MappedMutexGuard` and `MutexGuard` is that the
/// former doesn't support temporarily unlocking and re-locking, since that
/// could introduce soundness issues if the locked object is modified by another
/// thread.
///
/// This structure is created by the [`map`](MutexGuard::map) and
/// [`try_map`](MutexGuard::try_map), and
/// [`try_map_or_err`](MutexGuard::try_map_or_err) functions on [`MutexGuard`].
#[clippy::has_significant_drop]
#[must_use = "if unused the Mutex will immediately unlock"]
pub struct MappedMutexGuard<'a, R: RawMutex, T: ?Sized + 'a> {
    raw: &'a R,
    data: ExclusiveGuardData<T>,
    marker: PhantomData<R::GuardMarker>,
}

impl<'a, R: RawMutex + 'a, T: ?Sized + 'a> MappedMutexGuard<'a, R, T> {
    /// Makes a new `MappedMutexGuard` for a component of the locked data.
    ///
    /// This is an associated function that needs to be
    /// used as `MappedMutexGuard::map(...)`. A method would interfere with methods of
    /// the same name on the contents of the locked data.
    ///
    /// # Panics
    ///
    /// If `f` panics, the original guard is dropped.
    #[inline]
    pub fn map<U: ?Sized, F>(mut s: Self, f: F) -> MappedMutexGuard<'a, R, U>
    where
        F: FnOnce(&mut T) -> &mut U,
    {
        let raw = s.raw;
        let data = ExclusiveGuardData::new(f(unsafe { s.data.as_mut() }));
        mem::forget(s);
        MappedMutexGuard {
            raw,
            data,
            marker: PhantomData,
        }
    }

    /// Attempts to make a new `MappedMutexGuard` for a component of the
    /// locked data. The original guard is returned if the closure returns `None`.
    ///
    /// This is an associated function that needs to be
    /// used as `MappedMutexGuard::try_map(...)`. A method would interfere with methods of
    /// the same name on the contents of the locked data.
    ///
    /// # Panics
    ///
    /// If `f` panics, the original guard is dropped.
    #[inline]
    pub fn try_map<U: ?Sized, F>(mut s: Self, f: F) -> Result<MappedMutexGuard<'a, R, U>, Self>
    where
        F: FnOnce(&mut T) -> Option<&mut U>,
    {
        let raw = s.raw;
        let Some(data) = f(unsafe { s.data.as_mut() }) else {
            return Err(s);
        };
        let data = ExclusiveGuardData::new(data);
        mem::forget(s);
        Ok(MappedMutexGuard {
            raw,
            data,
            marker: PhantomData,
        })
    }

    /// Attempts to make a new `MappedMutexGuard` for a component of the
    /// locked data. The original guard is returned alongside arbitrary user data
    /// if the closure returns `Err`.
    ///
    /// This is an associated function that needs to be
    /// used as `MappedMutexGuard::try_map_or_err(...)`. A method would interfere with methods of
    /// the same name on the contents of the locked data.
    ///
    /// # Panics
    ///
    /// If `f` panics, the original guard is dropped.
    #[inline]
    pub fn try_map_or_err<U: ?Sized, F, E>(
        mut s: Self,
        f: F,
    ) -> Result<MappedMutexGuard<'a, R, U>, (Self, E)>
    where
        F: FnOnce(&mut T) -> Result<&mut U, E>,
    {
        let raw = s.raw;
        let data = match f(unsafe { s.data.as_mut() }) {
            Ok(data) => data,
            Err(e) => return Err((s, e)),
        };
        let data = ExclusiveGuardData::new(data);
        mem::forget(s);
        Ok(MappedMutexGuard {
            raw,
            data,
            marker: PhantomData,
        })
    }
}

impl<'a, R: RawMutexFair + 'a, T: ?Sized + 'a> MappedMutexGuard<'a, R, T> {
    /// Unlocks the mutex using a fair unlock protocol.
    ///
    /// A fair unlock hands the mutex directly to a waiting thread instead of
    /// allowing another thread to steal it. This can prevent starvation, but may
    /// reduce throughput by forcing a context switch.
    #[inline]
    #[track_caller]
    pub fn unlock_fair(s: Self) {
        // Safety: A MappedMutexGuard always holds the lock.
        unsafe {
            s.raw.unlock_fair();
        }
        mem::forget(s);
    }
}

impl<'a, R: RawMutex + 'a, T: ?Sized + 'a> Deref for MappedMutexGuard<'a, R, T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        unsafe { self.data.as_ref() }
    }
}

impl<'a, R: RawMutex + 'a, T: ?Sized + 'a> DerefMut for MappedMutexGuard<'a, R, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        unsafe { self.data.as_mut() }
    }
}

impl<'a, R: RawMutex + 'a, T: ?Sized + 'a> Drop for MappedMutexGuard<'a, R, T> {
    #[inline]
    fn drop(&mut self) {
        // Safety: A MappedMutexGuard always holds the lock.
        unsafe {
            self.raw.unlock();
        }
    }
}

impl<'a, R: RawMutex + 'a, T: fmt::Debug + ?Sized + 'a> fmt::Debug for MappedMutexGuard<'a, R, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<'a, R: RawMutex + 'a, T: fmt::Display + ?Sized + 'a> fmt::Display
    for MappedMutexGuard<'a, R, T>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

#[cfg(feature = "owning_ref")]
unsafe impl<'a, R: RawMutex + 'a, T: ?Sized + 'a> StableAddress for MappedMutexGuard<'a, R, T> {}
