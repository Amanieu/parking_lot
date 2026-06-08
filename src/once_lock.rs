use core::{
    cell::UnsafeCell,
    convert::Infallible,
    fmt,
    mem::MaybeUninit,
    panic::{RefUnwindSafe, UnwindSafe},
};

use crate::Once;

/// A synchronization primitive which can be used to initialize and store a
/// value exactly once.
///
/// This type builds upon [`Once`] to provide safe, one-time initialization of
/// data, allowing shared access to the initialized value afterwards.
///
/// It is commonly used for lazy initialization of global data, caches, or
/// resources that are expensive to construct.
///
/// # Differences from the standard library `OnceLock`
///
/// - Built on top of a lightweight [`Once`] (1 byte state).
///
/// # Examples
///
/// ```
/// use parking_lot::OnceLock;
///
/// static CELL: OnceLock<usize> = OnceLock::new();
///
/// fn get_value() -> usize {
///     *CELL.get_or_init(|| {
///         // compute value once
///         42
///     })
/// }
/// ```
pub struct OnceLock<T> {
    once: Once,
    value: UnsafeCell<MaybeUninit<T>>,
}

impl<T> OnceLock<T> {
    /// Creates a new uninitialized cell.
    #[must_use]
    #[inline]
    pub const fn new() -> Self {
        Self {
            once: Once::new(),
            value: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }

    /// Gets the reference to the underlying value.
    ///
    /// Returns `None` if the cell is uninitialized, or being initialized.
    /// This method never blocks.
    #[inline]
    pub fn get(&self) -> Option<&T> {
        if self.initialized() {
            // Safe b/c checked initialized
            Some(unsafe { self.get_unchecked() })
        } else {
            None
        }
    }

    /// Gets the mutable reference to the underlying value.
    ///
    /// Returns `None` if the cell is uninitialized.
    ///
    /// This method never blocks. Since it borrows the `OnceLock` mutably,
    /// it is statically guaranteed that no active borrows to the `OnceLock`
    /// exist, including from other threads.
    #[inline]
    pub fn get_mut(&mut self) -> Option<&mut T> {
        if self.initialized() {
            // Safe b/c checked initialized
            Some(unsafe { self.get_unchecked_mut() })
        } else {
            None
        }
    }

    /// Blocks the current thread until the cell is initialized.
    ///
    /// # Example
    ///
    /// Waiting for a computation on another thread to finish:
    /// ```rust
    /// use std::thread;
    /// use parking_lot::OnceLock;
    ///
    /// let value = OnceLock::new();
    ///
    /// thread::scope(|s| {
    ///     s.spawn(|| value.set(1 + 1));
    ///
    ///     let result = value.wait();
    ///     assert_eq!(result, &2);
    /// })
    /// ```
    #[inline]
    pub fn wait(&self) -> &T {
        self.once.wait();

        unsafe { self.get_unchecked() }
    }

    /// Initializes the contents of the cell to `value`.
    ///
    /// May block if another thread is currently attempting to initialize the cell. The cell is
    /// guaranteed to contain a value when `set` returns, though not necessarily the one provided.
    ///
    /// Returns `Ok(())` if the cell was uninitialized and
    /// `Err(value)` if the cell was already initialized.
    ///
    /// # Examples
    ///
    /// ```
    /// use parking_lot::OnceLock;
    ///
    /// static CELL: OnceLock<i32> = OnceLock::new();
    ///
    /// fn main() {
    ///     assert!(CELL.get().is_none());
    ///
    ///     std::thread::spawn(|| {
    ///         assert_eq!(CELL.set(92), Ok(()));
    ///     }).join().unwrap();
    ///
    ///     assert_eq!(CELL.set(62), Err(62));
    ///     assert_eq!(CELL.get(), Some(&92));
    /// }
    /// ```
    #[inline]
    pub fn set(&self, value: T) -> Result<(), T> {
        match self.try_insert(value) {
            Ok(_) => Ok(()),
            Err((_, value)) => Err(value),
        }
    }

    /// Initializes the contents of the cell to `value` if the cell was uninitialized,
    /// then returns a reference to it.
    ///
    /// May block if another thread is currently attempting to initialize the cell. The cell is
    /// guaranteed to contain a value when `try_insert` returns, though not necessarily the
    /// one provided.
    ///
    /// Returns `Ok(&value)` if the cell was uninitialized and
    /// `Err((&current_value, value))` if it was already initialized.
    ///
    /// # Examples
    ///
    /// ```
    /// use parking_lot::OnceLock;
    ///
    /// static CELL: OnceLock<i32> = OnceLock::new();
    ///
    /// fn main() {
    ///     assert!(CELL.get().is_none());
    ///
    ///     std::thread::spawn(|| {
    ///         assert_eq!(CELL.try_insert(92), Ok(&92));
    ///     }).join().unwrap();
    ///
    ///     assert_eq!(CELL.try_insert(62), Err((&92, 62)));
    ///     assert_eq!(CELL.get(), Some(&92));
    /// }
    /// ```
    #[inline]
    pub fn try_insert(&self, value: T) -> Result<&T, (&T, T)> {
        let mut value = Some(value);
        let res = self.get_or_init(|| value.take().unwrap());
        match value {
            None => Ok(res),
            Some(value) => Err((res, value)),
        }
    }

    /// Gets the contents of the cell, initializing it to `f()` if the cell
    /// was uninitialized.
    ///
    /// Many threads may call `get_or_init` concurrently with different
    /// initializing functions, but it is guaranteed that only one function
    /// will be executed if the function doesn't panic.
    ///
    /// # Panics
    ///
    /// If `f()` panics, the panic is propagated to the caller, and the cell
    /// remains uninitialized.
    ///
    /// It is an error to reentrantly initialize the cell from `f`. The
    /// exact outcome is unspecified. Current implementation deadlocks, but
    /// this may be changed to a panic in the future.
    ///
    /// # Examples
    ///
    /// ```
    /// use parking_lot::OnceLock;
    ///
    /// let cell = OnceLock::new();
    /// let value = cell.get_or_init(|| 92);
    /// assert_eq!(value, &92);
    /// let value = cell.get_or_init(|| unreachable!());
    /// assert_eq!(value, &92);
    /// ```
    #[inline]
    pub fn get_or_init<F>(&self, f: F) -> &T
    where
        F: FnOnce() -> T,
    {
        match self.get_or_try_init(|| Ok::<T, Infallible>(f())) {
            Ok(val) => val,
        }
    }

    /// Gets the mutable reference of the contents of the cell, initializing
    /// it to `f()` if the cell was uninitialized.
    ///
    /// This method never blocks. Since it borrows the `OnceLock` mutably,
    /// it is statically guaranteed that no active borrows to the `OnceLock`
    /// exist, including from other threads.
    ///
    /// # Panics
    ///
    /// If `f()` panics, the panic is propagated to the caller, and the cell
    /// remains uninitialized.
    ///
    /// # Examples
    ///
    /// ```
    /// use parking_lot::OnceLock;
    ///
    /// let mut cell = OnceLock::new();
    /// let value = cell.get_mut_or_init(|| 92);
    /// assert_eq!(*value, 92);
    ///
    /// *value += 2;
    /// assert_eq!(*value, 94);
    ///
    /// let value = cell.get_mut_or_init(|| unreachable!());
    /// assert_eq!(*value, 94);
    /// ```
    #[inline]
    pub fn get_mut_or_init<F>(&mut self, f: F) -> &mut T
    where
        F: FnOnce() -> T,
    {
        match self.get_mut_or_try_init(|| Ok::<T, Infallible>(f())) {
            Ok(val) => val,
        }
    }

    /// Gets the contents of the cell, initializing it to `f()` if
    /// the cell was uninitialized. If the cell was uninitialized
    /// and `f()` failed, an error is returned.
    ///
    /// # Panics
    ///
    /// If `f()` panics, the panic is propagated to the caller, and
    /// the cell remains uninitialized.
    ///
    /// It is an error to reentrantly initialize the cell from `f`.
    /// The exact outcome is unspecified. Current implementation
    /// deadlocks, but this may be changed to a panic in the future.
    ///
    /// # Examples
    ///
    /// ```
    /// use parking_lot::OnceLock;
    ///
    /// let cell = OnceLock::new();
    /// assert_eq!(cell.get_or_try_init(|| Err(())), Err(()));
    /// assert!(cell.get().is_none());
    /// let value = cell.get_or_try_init(|| -> Result<i32, ()> {
    ///     Ok(92)
    /// });
    /// assert_eq!(value, Ok(&92));
    /// assert_eq!(cell.get(), Some(&92))
    /// ```
    #[inline]
    pub fn get_or_try_init<F, E>(&self, f: F) -> Result<&T, E>
    where
        F: FnOnce() -> Result<T, E>,
    {
        // Fast path check
        if let Some(value) = self.get() {
            return Ok(value);
        }
        self.initialize(f)?;

        // SAFETY: The inner value has been initialized
        Ok(unsafe { self.get_unchecked() })
    }

    /// Gets the mutable reference of the contents of the cell, initializing
    /// it to `f()` if the cell was uninitialized. If the cell was uninitialized
    /// and `f()` failed, an error is returned.
    ///
    /// This method never blocks. Since it borrows the `OnceLock` mutably,
    /// it is statically guaranteed that no active borrows to the `OnceLock`
    /// exist, including from other threads.
    ///
    /// # Panics
    ///
    /// If `f()` panics, the panic is propagated to the caller, and
    /// the cell remains uninitialized.
    ///
    /// # Examples
    ///
    /// ```
    /// use parking_lot::OnceLock;
    ///
    /// let mut cell: OnceLock<u32> = OnceLock::new();
    ///
    /// // Failed attempts to initialize the cell do not change its contents
    /// assert!(cell.get_mut_or_try_init(|| "not a number!".parse()).is_err());
    /// assert!(cell.get().is_none());
    ///
    /// let value = cell.get_mut_or_try_init(|| "1234".parse());
    /// assert_eq!(value, Ok(&mut 1234));
    /// *value.unwrap() += 2;
    /// assert_eq!(cell.get(), Some(&1236))
    /// ```
    #[inline]
    pub fn get_mut_or_try_init<F, E>(&mut self, f: F) -> Result<&mut T, E>
    where
        F: FnOnce() -> Result<T, E>,
    {
        if self.get_mut().is_none() {
            self.initialize(f)?;
        }

        // SAFETY: The inner value has been initialized
        Ok(unsafe { self.get_unchecked_mut() })
    }

    /// Consumes the `OnceLock`, returning the wrapped value. Returns
    /// `None` if the cell was uninitialized.
    ///
    /// # Examples
    ///
    /// ```
    /// use parking_lot::OnceLock;
    ///
    /// let cell: OnceLock<String> = OnceLock::new();
    /// assert_eq!(cell.into_inner(), None);
    ///
    /// let cell = OnceLock::new();
    /// cell.set("hello".to_string()).unwrap();
    /// assert_eq!(cell.into_inner(), Some("hello".to_string()));
    /// ```
    #[inline]
    pub fn into_inner(mut self) -> Option<T> {
        self.take()
    }

    /// Takes the value out of this `OnceLock`, moving it back to an uninitialized state.
    ///
    /// Has no effect and returns `None` if the `OnceLock` was uninitialized.
    ///
    /// Since this method borrows the `OnceLock` mutably, it is statically guaranteed that
    /// no active borrows to the `OnceLock` exist, including from other threads.
    ///
    /// # Examples
    ///
    /// ```
    /// use parking_lot::OnceLock;
    ///
    /// let mut cell: OnceLock<String> = OnceLock::new();
    /// assert_eq!(cell.take(), None);
    ///
    /// let mut cell = OnceLock::new();
    /// cell.set("hello".to_string()).unwrap();
    /// assert_eq!(cell.take(), Some("hello".to_string()));
    /// assert_eq!(cell.get(), None);
    /// ```
    #[inline]
    pub fn take(&mut self) -> Option<T> {
        if self.initialized() {
            self.once = Once::new();
            // SAFETY: `self.value` is initialized and contains a valid `T`.
            // `self.once` is reset, so `initialized()` will be false again
            // which prevents the value from being read twice.
            unsafe { Some(self.value.get_mut().assume_init_read()) }
        } else {
            None
        }
    }

    #[inline]
    fn initialized(&self) -> bool {
        // Acquire load via `Once::state()`
        self.once.state().done()
    }

    #[cold]
    fn initialize<F, E>(&self, f: F) -> Result<(), E>
    where
        F: FnOnce() -> Result<T, E>,
    {
        let mut res: Result<(), E> = Ok(());
        let slot = &self.value;

        // Ignore poisoning from other threads
        // If another thread panics, then we'll be able to run our closure
        self.once.call_once_for_once_lock(|p| match f() {
            Ok(value) => {
                unsafe { (&mut *slot.get()).write(value) };

                // work around to match std behavior
                p.set_done();
            }
            Err(e) => {
                res = Err(e);

                // work around to match std behavior
                p.set_poison();
            }
        });

        res
    }

    /// # Safety
    ///
    /// The cell must be initialized
    #[inline]
    unsafe fn get_unchecked(&self) -> &T {
        debug_assert!(self.initialized());
        unsafe { (&*self.value.get()).assume_init_ref() }
    }

    /// # Safety
    ///
    /// The cell must be initialized
    #[inline]
    unsafe fn get_unchecked_mut(&mut self) -> &mut T {
        debug_assert!(self.initialized());
        unsafe { self.value.get_mut().assume_init_mut() }
    }
}

impl<T> Default for OnceLock<T> {
    /// Creates a new uninitialized cell.
    ///
    /// # Example
    ///
    /// ```
    /// use parking_lot::OnceLock;
    ///
    /// fn main() {
    ///     assert_eq!(OnceLock::<()>::new(), OnceLock::default());
    /// }
    /// ```
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

unsafe impl<T: Sync + Send> Sync for OnceLock<T> {}
unsafe impl<T: Send> Send for OnceLock<T> {}

impl<T: RefUnwindSafe + UnwindSafe> RefUnwindSafe for OnceLock<T> {}
impl<T: UnwindSafe> UnwindSafe for OnceLock<T> {}

impl<T: fmt::Debug> fmt::Debug for OnceLock<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_tuple("OnceLock");
        match self.get() {
            Some(v) => d.field(v),
            None => d.field(&format_args!("<uninit>")),
        };
        d.finish()
    }
}

impl<T: Clone> Clone for OnceLock<T> {
    #[inline]
    fn clone(&self) -> OnceLock<T> {
        let cell = Self::new();
        if let Some(value) = self.get() {
            match cell.set(value.clone()) {
                Ok(()) => (),
                Err(_) => unreachable!(),
            }
        }
        cell
    }
}

impl<T> From<T> for OnceLock<T> {
    /// Creates a new cell with its contents set to `value`.
    ///
    /// # Example
    ///
    /// ```
    /// use parking_lot::OnceLock;
    ///
    /// # fn main() -> Result<(), i32> {
    /// let a = OnceLock::from(3);
    /// let b = OnceLock::new();
    /// b.set(3)?;
    /// assert_eq!(a, b);
    /// Ok(())
    /// # }
    /// ```
    #[inline]
    fn from(value: T) -> Self {
        let cell = Self::new();
        match cell.set(value) {
            Ok(()) => cell,
            Err(_) => unreachable!(),
        }
    }
}

impl<T: PartialEq> PartialEq for OnceLock<T> {
    /// Equality for two `OnceLock`s.
    ///
    /// Two `OnceLock`s are equal if they either both contain values and their
    /// values are equal, or if neither contains a value.
    ///
    /// # Examples
    ///
    /// ```
    /// use parking_lot::OnceLock;
    ///
    /// let five = OnceLock::new();
    /// five.set(5).unwrap();
    ///
    /// let also_five = OnceLock::new();
    /// also_five.set(5).unwrap();
    ///
    /// assert!(five == also_five);
    ///
    /// assert!(OnceLock::<u32>::new() == OnceLock::<u32>::new());
    /// ```
    #[inline]
    fn eq(&self, other: &OnceLock<T>) -> bool {
        self.get() == other.get()
    }
}

impl<T: Eq> Eq for OnceLock<T> {}

impl<T> Drop for OnceLock<T> {
    #[inline]
    fn drop(&mut self) {
        if self.initialized() {
            unsafe { self.value.get_mut().assume_init_drop() };
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{
        sync::{
            Arc, Barrier,
            atomic::{AtomicBool, AtomicUsize, Ordering},
        },
        thread,
    };

    use super::*;

    #[test]
    fn once_lock_smoke() {
        let cell = OnceLock::new();

        assert!(cell.get().is_none());

        cell.set(42).unwrap();

        assert_eq!(cell.get(), Some(&42));
    }

    #[test]
    fn once_lock_get_or_init() {
        let cell = OnceLock::new();

        let v1 = cell.get_or_init(|| 10);
        let v2 = cell.get_or_init(|| 20);

        assert_eq!(*v1, 10);
        assert!(core::ptr::eq(v1, v2));
    }

    #[test]
    fn once_lock_concurrent_init() {
        const N: usize = 8;

        let cell = Arc::new(OnceLock::new());
        let barrier = Arc::new(Barrier::new(N));

        let mut handles = Vec::new();

        for _ in 0..N {
            let cell = cell.clone();
            let barrier = barrier.clone();

            handles.push(thread::spawn(move || {
                barrier.wait();
                let v = cell.get_or_init(|| 1234);
                assert_eq!(*v, 1234);
            }));
        }

        for h in handles {
            h.join().unwrap();
        }

        assert_eq!(cell.get(), Some(&1234));
    }

    // copied from std doc test
    #[test]
    fn once_lock_get_or_try_init() {
        let cell = OnceLock::new();
        assert_eq!(cell.get_or_try_init(|| Err(())), Err(()));
        assert!(cell.get().is_none());
        let value = cell.get_or_try_init(|| -> Result<i32, ()> { Ok(92) });
        assert_eq!(value, Ok(&92));
        assert_eq!(cell.get(), Some(&92))
    }

    // copied from std doc test
    #[test]
    fn once_lock_get_mut_or_try_init() {
        let mut cell: OnceLock<u32> = OnceLock::new();

        // Failed attempts to initialize the cell do not change its contents
        assert!(
            cell.get_mut_or_try_init(|| "not a number!".parse())
                .is_err()
        );
        assert!(cell.get().is_none());

        let value = cell.get_mut_or_try_init(|| "1234".parse());
        assert_eq!(value, Ok(&mut 1234));

        *value.unwrap() += 2;
        assert_eq!(cell.get(), Some(&1236));
    }

    #[test]
    fn once_lock_observe_during_init() {
        let cell = Arc::new(OnceLock::new());
        let entered = Arc::new(AtomicBool::new(false));
        let started = Arc::new(AtomicBool::new(false));

        let cell2 = cell.clone();
        let entered2 = entered.clone();
        let started2 = started.clone();

        let t = thread::spawn(move || {
            cell2.get_or_init(|| {
                // signal that initialization has started
                entered2.store(true, Ordering::SeqCst);
                // wait until the main thread has observed that the value is still uninitialized
                while !started2.load(Ordering::SeqCst) {
                    std::hint::spin_loop();
                }
                99
            });
        });

        // wait for the cell thread to enter
        while !entered.load(Ordering::SeqCst) {
            std::hint::spin_loop();
        }
        assert!(cell.get().is_none());

        // signal that the main thread has finished observing the uninitialized state
        started.store(true, Ordering::SeqCst);
        t.join().unwrap();

        assert_eq!(cell.get(), Some(&99));
    }

    #[test]
    fn once_lock_only_once() {
        let cell = OnceLock::new();
        let counter = AtomicUsize::new(0);

        let f = || {
            counter.fetch_add(1, Ordering::SeqCst);
            7
        };

        let _ = cell.get_or_init(f);
        // the initializer must only run once
        let _ = cell.get_or_init(f);

        assert_eq!(counter.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn once_lock_wait() {
        let cell = Arc::new(OnceLock::new());
        let entered = Arc::new(AtomicBool::new(false));

        let cell2 = cell.clone();
        let entered2 = entered.clone();

        let t = thread::spawn(move || {
            // signal that the waiting thread has started
            entered2.store(true, Ordering::SeqCst);
            let v = cell2.wait();
            assert_eq!(*v, 99);
        });

        // wait for the spawned thread to start waiting
        while !entered.load(Ordering::SeqCst) {
            std::hint::spin_loop();
        }
        cell.set(99).unwrap();

        t.join().unwrap();
    }

    #[test]
    fn once_lock_init_panic() {
        let cell = Arc::new(OnceLock::new());
        let cell2 = cell.clone();

        let _ = thread::spawn(move || {
            let _ = std::panic::catch_unwind(|| {
                cell2.get_or_init(|| panic!("init failed"));
            });
        })
        .join();

        // A panic during initialization must not leave the cell initialized
        assert!(cell.get().is_none());

        let v = cell.get_or_init(|| 42);
        assert_eq!(*v, 42);
    }

    #[test]
    fn once_lock_set() {
        let cell = OnceLock::new();

        // verify both insertion and returned value semantics
        assert!(cell.set(1).is_ok());
        assert_eq!(cell.set(2), Err(2));

        assert_eq!(cell.get(), Some(&1));
    }

    #[test]
    fn once_lock_try_insert() {
        let cell = OnceLock::new();

        // verify both insertion and returned value semantics
        assert_eq!(cell.try_insert(1), Ok(&1));
        assert_eq!(cell.try_insert(2), Err((&1, 2)));

        assert_eq!(cell.get(), Some(&1));
    }

    #[test]
    fn once_lock_take() {
        let mut cell = OnceLock::new();

        cell.set(5).unwrap();
        assert_eq!(cell.take(), Some(5));

        assert!(cell.get().is_none());

        cell.set(10).unwrap();
        assert_eq!(cell.get(), Some(&10));
    }

    #[test]
    fn once_lock_drop() {
        struct DropCounter<'a>(&'a AtomicUsize);

        impl<'a> Drop for DropCounter<'a> {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }

        let counter = AtomicUsize::new(0);

        {
            let cell = OnceLock::new();
            cell.set(DropCounter(&counter)).ok().unwrap();
        }

        assert_eq!(counter.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn once_lock_mixed_behavior() {
        const N: usize = 12;
        const { assert!(N.is_multiple_of(3)) };

        let cell = Arc::new(OnceLock::new());
        let barrier = Arc::new(Barrier::new(N));

        let mut handles = Vec::new();

        for i in 0..N / 3 {
            let cell = cell.clone();
            let barrier = barrier.clone();
            if i.is_multiple_of(2) {
                handles.push(thread::spawn(move || {
                    barrier.wait();
                    cell.get_or_try_init(|| -> Result<i32, ()> { Ok(42) })
                        .ok()
                        .copied()
                }));
            } else {
                handles.push(thread::spawn(move || {
                    barrier.wait();
                    cell.get_or_try_init(|| -> Result<i32, ()> { Err(()) })
                        .ok()
                        .copied()
                }));
            }
        }

        for _ in 0..N / 3 {
            let cell = cell.clone();
            let barrier = barrier.clone();
            handles.push(thread::spawn(move || {
                barrier.wait();
                let v = cell.get_or_init(|| 42);
                Some(*v)
            }));
        }

        for _ in 0..N / 3 {
            let cell = cell.clone();
            let barrier = barrier.clone();
            handles.push(thread::spawn(move || {
                barrier.wait();
                let v = cell.wait();
                Some(*v)
            }));
        }

        for h in handles {
            if let Some(v) = h.join().unwrap() {
                assert_eq!(v, 42);
            };
        }

        assert_eq!(cell.get(), Some(&42));
    }
}
