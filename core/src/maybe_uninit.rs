//! This module contains a re-export or vendored version of `core::mem::MaybeUninit` depending
//! on which Rust version it's compiled for.
//!
//! Remove this module and use `core::mem::MaybeUninit` directly when dropping support for <1.36
#![allow(dead_code)]

#[cfg(has_maybe_uninit)]
pub use core::mem::MaybeUninit;

#[cfg(not(has_maybe_uninit))]
use core::mem::ManuallyDrop;

/// Copied from `core::mem::MaybeUninit` to support Rust older than 1.36
#[cfg(not(has_maybe_uninit))]
pub union MaybeUninit<T: Copy> {
    uninit: (),
    value: ManuallyDrop<T>,
}

#[cfg(not(has_maybe_uninit))]
impl<T: Copy> MaybeUninit<T> {
    #[inline(always)]
    pub fn uninit() -> MaybeUninit<T> {
        MaybeUninit { uninit: () }
    }

    #[inline(always)]
    pub fn as_ptr(&self) -> *const T {
        unsafe { &*self.value as *const T }
    }

    #[inline(always)]
    pub fn as_mut_ptr(&mut self) -> *mut T {
        unsafe { &mut *self.value as *mut T }
    }

    #[inline(always)]
    pub unsafe fn assume_init(self) -> T {
        ManuallyDrop::into_inner(self.value)
    }
}
