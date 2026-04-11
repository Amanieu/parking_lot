use std::{
    cell::UnsafeCell,
    convert::Infallible,
    fmt,
    mem::MaybeUninit,
    panic::{RefUnwindSafe, UnwindSafe},
};

use crate::Once;

pub struct OnceLock<T> {
    once: Once,
    value: UnsafeCell<MaybeUninit<T>>,
}

impl<T> OnceLock<T> {
    #[must_use]
    #[inline]
    pub const fn new() -> Self {
        Self {
            once: Once::new(),
            value: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }

    #[inline]
    pub fn get(&self) -> Option<&T> {
        if self.initialized() {
            Some(unsafe { self.get_unchecked() })
        } else {
            None
        }
    }

    #[inline]
    pub fn get_mut(&mut self) -> Option<&mut T> {
        if self.initialized() {
            Some(unsafe { self.get_unchecked_mut() })
        } else {
            None
        }
    }

    #[inline]
    pub fn wait(&self) -> &T {
        self.once.wait();

        unsafe { self.get_unchecked() }
    }

    #[inline]
    pub fn set(&self, value: T) -> Result<(), T> {
        match self.try_insert(value) {
            Ok(_) => Ok(()),
            Err((_, value)) => Err(value),
        }
    }

    #[inline]
    pub fn try_insert(&self, value: T) -> Result<&T, (&T, T)> {
        let mut value = Some(value);
        let res = self.get_or_init(|| value.take().unwrap());
        match value {
            None => Ok(res),
            Some(value) => Err((res, value)),
        }
    }

    #[inline]
    pub fn get_or_init<F>(&self, f: F) -> &T
    where
        F: FnOnce() -> T,
    {
        match self.get_or_try_init(|| Ok::<T, Infallible>(f())) {
            Ok(val) => val,
        }
    }

    #[inline]
    pub fn get_mut_or_init<F>(&mut self, f: F) -> &mut T
    where
        F: FnOnce() -> T,
    {
        match self.get_mut_or_try_init(|| Ok::<T, Infallible>(f())) {
            Ok(val) => val,
        }
    }

    #[inline]
    pub fn get_or_try_init<F, E>(&self, f: F) -> Result<&T, E>
    where
        F: FnOnce() -> Result<T, E>,
    {
        if let Some(value) = self.get() {
            return Ok(value);
        }
        self.initialize(f)?;

        Ok(unsafe { self.get_unchecked() })
    }

    #[inline]
    pub fn get_mut_or_try_init<F, E>(&mut self, f: F) -> Result<&mut T, E>
    where
        F: FnOnce() -> Result<T, E>,
    {
        if self.get_mut().is_none() {
            self.initialize(f)?;
        }

        Ok(unsafe { self.get_unchecked_mut() })
    }

    #[inline]
    pub fn into_inner(mut self) -> Option<T> {
        self.take()
    }

    #[inline]
    pub fn take(&mut self) -> Option<T> {
        if self.initialized() {
            self.once = Once::new();
            unsafe { Some(self.value.get_mut().assume_init_read()) }
        } else {
            None
        }
    }

    #[inline]
    fn initialized(&self) -> bool {
        self.once.state().done()
    }

    #[cold]
    fn initialize<F, E>(&self, f: F) -> Result<(), E>
    where
        F: FnOnce() -> Result<T, E>,
    {
        let mut res: Result<(), E> = Ok(());
        let slot = &self.value;

        self.once.call_once_force(|_| match f() {
            Ok(value) => {
                unsafe { (&mut *slot.get()).write(value) };
            }
            Err(e) => {
                res = Err(e);
            }
        });
        res
    }

    #[inline]
    unsafe fn get_unchecked(&self) -> &T {
        debug_assert!(self.initialized());
        unsafe { (&*self.value.get()).assume_init_ref() }
    }

    #[inline]
    unsafe fn get_unchecked_mut(&mut self) -> &mut T {
        debug_assert!(self.initialized());
        unsafe { self.value.get_mut().assume_init_mut() }
    }
}

impl<T> Default for OnceLock<T> {
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

    #[test]
    fn once_lock_observe_during_init() {
        let cell = Arc::new(OnceLock::new());
        let started = Arc::new(AtomicBool::new(false));
        let entered = Arc::new(AtomicBool::new(false));

        let cell2 = cell.clone();
        let started2 = started.clone();
        let entered2 = entered.clone();

        let t = thread::spawn(move || {
            cell2.get_or_init(|| {
                entered2.store(true, Ordering::SeqCst);
                while !started2.load(Ordering::SeqCst) {
                    std::hint::spin_loop();
                }
                99
            });
        });

        while !entered.load(Ordering::SeqCst) {
            std::hint::spin_loop();
        }
        assert!(cell.get().is_none());

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
        let _ = cell.get_or_init(f);

        assert_eq!(counter.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn once_lock_wait() {
        let cell = Arc::new(OnceLock::new());
        let started = Arc::new(AtomicBool::new(false));

        let cell2 = cell.clone();
        let started2 = started.clone();

        let t = thread::spawn(move || {
            started2.store(true, Ordering::SeqCst);
            let v = cell2.wait();
            assert_eq!(*v, 99);
        });

        while !started.load(Ordering::SeqCst) {
            std::hint::spin_loop();
        }
        cell.set(99).unwrap();

        t.join().unwrap();
    }

    #[test]
    fn once_lock_poison() {
        let cell = Arc::new(OnceLock::new());
        let cell2 = cell.clone();

        let _ = thread::spawn(move || {
            let _ = std::panic::catch_unwind(|| {
                cell2.get_or_init(|| panic!("init failed"));
            });
        })
        .join();

        let v = cell.get_or_init(|| 42);
        assert_eq!(*v, 42);
    }

    #[test]
    fn once_lock_try_insert() {
        let cell = OnceLock::new();

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
        let cell = Arc::new(OnceLock::new());

        let mut handles = Vec::new();

        for _ in 0..4 {
            let cell = cell.clone();
            handles.push(thread::spawn(move || {
                let v = cell.get_or_init(|| 42);
                assert_eq!(*v, 42);
            }));
        }

        for _ in 0..4 {
            let cell = cell.clone();
            handles.push(thread::spawn(move || {
                let v = cell.wait();
                assert_eq!(*v, 42);
            }));
        }

        for h in handles {
            h.join().unwrap();
        }

        assert_eq!(cell.get(), Some(&42));
    }

    #[test]
    fn once_lock_frob() {
        const N: usize = 8;
        const M: usize = if cfg!(miri) { 100 } else { 1000 };

        let cell = Arc::new(OnceLock::new());
        let mut handles = Vec::new();

        for _ in 0..N {
            let cell = cell.clone();
            handles.push(thread::spawn(move || {
                for _ in 0..M {
                    let _ = cell.get_or_init(|| 123);
                }
            }));
        }

        for h in handles {
            h.join().unwrap();
        }

        assert_eq!(cell.get(), Some(&123));
    }
}
