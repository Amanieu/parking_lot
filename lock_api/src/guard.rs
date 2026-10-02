use core::ptr::NonNull;

/// A raw pointer carrying shared guard access to `T`.
pub(crate) struct SharedGuardData<T: ?Sized>(NonNull<T>);

impl<T: ?Sized> SharedGuardData<T> {
    #[inline]
    pub(crate) fn new(data: &T) -> Self {
        Self(NonNull::from(data))
    }

    #[inline]
    pub(crate) unsafe fn as_ref(&self) -> &T {
        unsafe { self.0.as_ref() }
    }
}

// SAFETY: Moving this pointer between threads only permits shared access to `T`,
// which is safe when `T: Sync`.
unsafe impl<T: Sync + ?Sized> Send for SharedGuardData<T> {}
// SAFETY: Sharing this pointer between threads only permits shared access to
// `T`, which is safe when `T: Sync`.
unsafe impl<T: Sync + ?Sized> Sync for SharedGuardData<T> {}

/// A raw pointer carrying exclusive guard access to `T`.
// This deliberately uses `*mut T` instead of `NonNull<T>` to preserve the
// invariance of exclusive access over `T`.
pub(crate) struct ExclusiveGuardData<T: ?Sized>(*mut T);

impl<T: ?Sized> ExclusiveGuardData<T> {
    #[inline]
    pub(crate) fn new(data: &mut T) -> Self {
        Self(data)
    }

    #[inline]
    pub(crate) unsafe fn as_ref(&self) -> &T {
        unsafe { self.0.as_ref_unchecked() }
    }

    #[inline]
    pub(crate) unsafe fn as_mut(&mut self) -> &mut T {
        unsafe { self.0.as_mut_unchecked() }
    }
}

// SAFETY: Moving this pointer transfers exclusive access to `T`, which is safe
// when `T: Send`.
unsafe impl<T: Send + ?Sized> Send for ExclusiveGuardData<T> {}
// SAFETY: A shared reference to this pointer only permits shared access to `T`,
// which is safe when `T: Sync`.
unsafe impl<T: Sync + ?Sized> Sync for ExclusiveGuardData<T> {}
