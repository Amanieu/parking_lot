/// A raw pointer carrying shared guard access to `T`.
pub(crate) struct SharedGuardData<T: ?Sized>(*const T);

impl<T: ?Sized> SharedGuardData<T> {
    #[inline]
    pub(crate) fn new(data: *const T) -> Self {
        Self(data)
    }

    #[inline]
    pub(crate) fn as_ptr(&self) -> *const T {
        self.0
    }
}

// SAFETY: Moving this pointer between threads only permits shared access to `T`,
// which is safe when `T: Sync`.
unsafe impl<T: Sync + ?Sized> Send for SharedGuardData<T> {}
// SAFETY: Sharing this pointer between threads only permits shared access to
// `T`, which is safe when `T: Sync`.
unsafe impl<T: Sync + ?Sized> Sync for SharedGuardData<T> {}

/// A raw pointer carrying exclusive guard access to `T`.
pub(crate) struct ExclusiveGuardData<T: ?Sized>(*mut T);

impl<T: ?Sized> ExclusiveGuardData<T> {
    #[inline]
    pub(crate) fn new(data: *mut T) -> Self {
        Self(data)
    }

    #[inline]
    pub(crate) fn as_ptr(&self) -> *mut T {
        self.0
    }
}

// SAFETY: Moving this pointer transfers exclusive access to `T`, which is safe
// when `T: Send`.
unsafe impl<T: Send + ?Sized> Send for ExclusiveGuardData<T> {}
// SAFETY: A shared reference to this pointer only permits shared access to `T`,
// which is safe when `T: Sync`.
unsafe impl<T: Sync + ?Sized> Sync for ExclusiveGuardData<T> {}
