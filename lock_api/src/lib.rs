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

#![no_std]
#![warn(missing_docs)]
#![warn(rust_2018_idioms)]

#[macro_use]
extern crate scopeguard;

#[cfg(feature = "arc_lock")]
extern crate alloc;

/// Marker type which indicates that the Guard type for a lock is `Send`.
pub struct GuardSend(());

/// Marker type which indicates that the Guard type for a lock is not `Send`.
pub struct GuardNoSend(*mut ());

unsafe impl Sync for GuardNoSend {}

/// Simple macro to reduce code deduplication between locking variants.
macro_rules! impl_lock {
    (
        // Impl block
        impl
        // Custom-grafted generics
        <
            $lname: ident: $lbound: ident, 
            $([Gen] $gname: ident: $gbound: ident,)? 
            $tname: ident: ?Sized
        >
        // Lock type
        $ty: ty {

        // Methods
        $(
            $(#[$attr: meta])*
            $vis: vis fn $name: ident
            (&$this: ident $(,)? $($arg: ident: $argty: ty),* $(,)?) -> $ret: ty {
            lock: $lock: expr;
            guard: $guard: expr;
            guard_arc: $guard_arc: expr;
            } => $arc_name: ident -> $arc_ret: ty;
        )*

        }
    ) => {
        impl<
            $lname: $lbound,
            $($gname: $gbound,)?
            $tname: ?Sized
        > $ty {

            $(
                $(#[$attr])*
                #[allow(clippy::redundant_closure_call)]
                $vis fn $name
                (&$this, $($arg: $argty),*) -> $ret {
                    let lock = $lock;
                    ($guard)(lock)
                }

                $(#[$attr])*
                #[doc = ""]
                #[doc = "This method requires the lock to be wrapped in an `Arc`, but returns"]
                #[doc = "a guard which does not have any lifetime requirements."]
                #[cfg(feature = "arc_lock")]
                #[allow(clippy::redundant_closure_call)]
                $vis fn $arc_name
                ($this: alloc::sync::Arc<Self>, $($arg: $argty),*) -> $arc_ret {
                    let lock = $lock;
                    ($guard_arc)(lock)
                }
            )*

        }
    }
}

mod mutex;
pub use crate::mutex::*;

mod remutex;
pub use crate::remutex::*;

mod rwlock;
pub use crate::rwlock::*;
