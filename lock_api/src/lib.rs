// Copyright 2018 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! This library provides type-safe and fully-featured `Mutex` and `RwLock`
//! types which wrap a simple raw mutex or rwlock type. This has several
//! benefits: not only does it eliminate a large portion of the work in
//! implementing custom lock types, it also allows users to write code which is
//! generic with regards to different lock implementations.
//!
//! Basic usage of this crate is very straightforward:
//!
//! 1. Create a raw lock type. This should only contain the lock state, not any
//!    data protected by the lock.
//! 2. Implement the `RawMutex` trait for your custom lock type.
//! 3. Export your mutex as a type alias for `lock_api::Mutex`, and
//!    your mutex guard as a type alias for `lock_api::MutexGuard`.
//!    See the [example](#example) below for details.
//!
//! This process is similar for RwLocks, except that two guards need to be
//! exported instead of one. (Or 3 guards if your type supports upgradable read
//! locks, see [extension traits](#extension-traits) below for details)
//!
//! # Example
//!
//! ```
//! use lock_api::{RawMutex, Mutex, GuardSend};
//! use std::sync::atomic::{AtomicBool, Ordering};
//!
//! // 1. Define our raw lock type
//! pub struct RawSpinlock(AtomicBool);
//!
//! // 2. Implement RawMutex for this type
//! unsafe impl RawMutex for RawSpinlock {
//!     const INIT: RawSpinlock = RawSpinlock(AtomicBool::new(false));
//!
//!     // A spinlock guard can be sent to another thread and unlocked there
//!     type GuardMarker = GuardSend;
//!
//!     fn lock(&self) {
//!         // Note: This isn't the best way of implementing a spinlock, but it
//!         // suffices for the sake of this example.
//!         while !self.try_lock() {}
//!     }
//!
//!     fn try_lock(&self) -> bool {
//!         self.0
//!             .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
//!             .is_ok()
//!     }
//!
//!     unsafe fn unlock(&self) {
//!         self.0.store(false, Ordering::Release);
//!     }
//! }
//!
//! // 3. Export the wrappers. This are the types that your users will actually use.
//! pub type Spinlock<T> = lock_api::Mutex<RawSpinlock, T>;
//! pub type SpinlockGuard<'a, T> = lock_api::MutexGuard<'a, RawSpinlock, T>;
//! ```
//!
//! # Extension traits
//!
//! In addition to basic locking & unlocking functionality, you have the option
//! of exposing additional functionality in your lock types by implementing
//! additional traits for it. Examples of extension features include:
//!
//! - Fair unlocking (`RawMutexFair`, `RawRwLockFair`)
//! - Lock timeouts (`RawMutexTimed`, `RawRwLockTimed`)
//! - Downgradable write locks (`RawRwLockDowngradable`)
//! - Recursive read locks (`RawRwLockRecursive`)
//! - Upgradable read locks (`RawRwLockUpgrade`)
//!
//! The `Mutex` and `RwLock` wrappers will automatically expose this additional
//! functionality if the raw lock type implements these extension traits.
//!
//! # Cargo features
//!
//! This crate supports three cargo features:
//!
//! - `owning_ref`: Allows your lock types to be used with the `owning_ref` crate.
//! - `arc_lock`: Enables locking from an `Arc`. This enables types such as `ArcMutexGuard`. Note that this
//!   requires the `alloc` crate to be present.
//! - `nightly`: Enables nightly-only features. At the moment the only such
//!   feature is `const fn` constructors for lock types.

#![no_std]
#![warn(missing_docs)]
#![warn(rust_2018_idioms)]
#![cfg_attr(feature = "nightly", feature(const_fn_trait_bound))]

#[macro_use]
extern crate scopeguard;

#[cfg(feature = "arc_lock")]
extern crate alloc;

/// Marker type which indicates that the Guard type for a lock is `Send`.
pub struct GuardSend(());

/// Marker type which indicates that the Guard type for a lock is not `Send`.
pub struct GuardNoSend(*mut ());

unsafe impl Sync for GuardNoSend {}

mod mutex;
pub use crate::mutex::*;

mod remutex;
pub use crate::remutex::*;

mod rwlock;
pub use crate::rwlock::*;

/// A "shim trait" to allow generalizing over functions which return some generic
/// type which may borrow elements of its arguments, but without specifying that
/// the return type is `&`, `&mut` or something else concrete. This allows using
/// HRTB to force a caller to supply a function which works for any lifetime,
/// and therefore avoids the caller relying on a specific lifetime for the
/// argument, which can cause UB if the inner data lives for the static lifetime.
///
/// It also allows the output type to depend on the input type, which is important
/// when using lifetimes in HRTBs but is not possible with the stable syntax for
/// the `Fn` traits.
pub trait FnOnceShim<'a, T: 'a> {
    /// Equivalent to `std::ops::FnOnce::Output`.
    type Output: 'a;

    /// Equivalent to `std::ops::FnOnce::call`
    fn call(self, input: T) -> Self::Output;
}

impl<'a, F, In, Out> FnOnceShim<'a, In> for F
where
    F: FnOnce(In) -> Out,
    In: 'a,
    Out: 'a,
{
    type Output = Out;

    fn call(self, input: In) -> Self::Output {
        self(input)
    }
}

/// As `FnOnceShim`, but specialized for functions which return an `Option` (used
/// for `try_map`).
pub trait FnOnceOptionShim<'a, T: 'a> {
    /// Equivalent to `std::ops::FnOnce::Output`.
    type Output: 'a;

    /// Equivalent to `std::ops::FnOnce::call`
    fn call(self, input: T) -> Option<Self::Output>;
}

impl<'a, F, In, Out> FnOnceOptionShim<'a, In> for F
where
    F: FnOnce(In) -> Option<Out>,
    In: 'a,
    Out: 'a,
{
    type Output = Out;

    fn call(self, input: In) -> Option<Self::Output> {
        self(input)
    }
}

/// As `FnOnceShim`, but specialized for functions which return an `Result` (used
/// for `try_map`).
pub trait FnOnceResultShim<'a, T: 'a> {
    /// Equivalent to `std::ops::FnOnce::Output`.
    type Output: 'a;
    /// Equivalent to `std::ops::FnOnce::Output`.
    type Error: 'a;

    /// Equivalent to `std::ops::FnOnce::call`
    fn call(self, input: T) -> Result<Self::Output, Self::Error>;
}

impl<'a, F, In, Out, Error> FnOnceResultShim<'a, In> for F
where
    F: FnOnce(In) -> Result<Out, Error>,
    In: 'a,
    Out: 'a,
    Error: 'a,
{
    type Output = Out;
    type Error = Error;

    fn call(self, input: In) -> Result<Self::Output, Self::Error> {
        self(input)
    }
}
