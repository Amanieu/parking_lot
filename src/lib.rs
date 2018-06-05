// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! This library provides implementations of `Mutex`, `RwLock`, `Condvar` and
//! `Once` that are smaller, faster and more flexible than those in the Rust
//! standard library. It also provides a `ReentrantMutex` type.

#![warn(missing_docs)]
#![cfg_attr(feature = "nightly", feature(const_fn))]
#![cfg_attr(feature = "nightly", feature(integer_atomics))]
#![cfg_attr(feature = "nightly", feature(asm))]

extern crate parking_lot_core;
extern crate lock_api;

mod util;
mod elision;
mod raw_mutex;
mod raw_rwlock;
mod condvar;
mod mutex;
mod remutex;
mod rwlock;
mod once;

#[cfg(feature = "deadlock_detection")]
pub mod deadlock;
#[cfg(not(feature = "deadlock_detection"))]
mod deadlock;

pub use once::{Once, OnceState, ONCE_INIT};
pub use mutex::{Mutex, MutexGuard};
pub use remutex::{ReentrantMutex, ReentrantMutexGuard};
pub use condvar::{Condvar, WaitTimeoutResult};
pub use rwlock::{RwLock, RwLockReadGuard, RwLockUpgradableReadGuard, RwLockWriteGuard};
