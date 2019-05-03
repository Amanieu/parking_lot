// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! This library exposes a low-level API for creating your own efficient
//! synchronization primitives.
//!
//! # The parking lot
//!
//! To keep synchronization primitives small, all thread queuing and suspending
//! functionality is offloaded to the *parking lot*. The idea behind this is based
//! on the Webkit [`WTF::ParkingLot`](https://webkit.org/blog/6161/locking-in-webkit/)
//! class, which essentially consists of a hash table mapping of lock addresses
//! to queues of parked (sleeping) threads. The Webkit parking lot was itself
//! inspired by Linux [futexes](http://man7.org/linux/man-pages/man2/futex.2.html),
//! but it is more powerful since it allows invoking callbacks while holding a
//! queue lock.
//!
//! There are two main operations that can be performed on the parking lot:
//!
//!  - *Parking* refers to suspending the thread while simultaneously enqueuing it
//! on a queue keyed by some address.
//! - *Unparking* refers to dequeuing a thread from a queue keyed by some address
//! and resuming it.
//!
//! See the documentation of the individual functions for more details.
//!
//! # Building custom synchronization primitives
//!
//! Building custom synchronization primitives is very simple since the parking
//! lot takes care of all the hard parts for you. A simple example for a
//! custom primitive would be to integrate a `Mutex` inside another data type.
//! Since a mutex only requires 2 bits, it can share space with other data.
//! For example, one could create an `ArcMutex` type that combines the atomic
//! reference count and the two mutex bits in the same atomic word.

#![warn(missing_docs)]
#![warn(rust_2018_idioms)]
#![cfg_attr(
    all(
        not(feature = "i-am-libstd"),
        target_env = "sgx",
        target_vendor = "fortanix"
    ),
    feature(sgx_platform)
)]
#![cfg_attr(
    all(
        not(feature = "i-am-libstd"),
        feature = "nightly",
        target_arch = "wasm32",
        target_feature = "atomics"
    ),
    feature(checked_duration_since, stdsimd)
)]
#![cfg_attr(
    all(feature = "nightly", target_os = "cloudabi",),
    feature(thread_local, checked_duration_since)
)]

#[cfg(not(feature = "i-am-libstd"))]
use cfg_if::cfg_if;

mod libstd {
    #[cfg(feature = "i-am-libstd")]
    pub use crate::*;
    #[cfg(not(feature = "i-am-libstd"))]
    pub use std::*;
}

cfg_if! {
    if #[cfg(all(any(has_sized_atomics, feature = "i-am-libstd"), target_os = "linux"))] {
        #[path = "thread_parker/linux.rs"]
        mod thread_parker;
    } else if #[cfg(unix)] {
        #[path = "thread_parker/unix.rs"]
        mod thread_parker;
    } else if #[cfg(windows)] {
        #[path = "thread_parker/windows/mod.rs"]
        mod thread_parker;
    } else if #[cfg(all(any(has_sized_atomics, feature = "i-am-libstd"), target_os = "redox"))] {
        #[path = "thread_parker/redox.rs"]
        mod thread_parker;
    } else if #[cfg(all(target_env = "sgx", target_vendor = "fortanix"))] {
        #[path = "thread_parker/sgx.rs"]
        mod thread_parker;
    } else if #[cfg(all(
        any(feature = "nightly", feature = "i-am-libstd"),
        target_arch = "wasm32",
        target_feature = "atomics"
    ))] {
        #[path = "thread_parker/wasm.rs"]
        mod thread_parker;
    } else if #[cfg(all(any(feature = "nightly", feature = "i-am-libstd"), target_os = "cloudabi"))] {
        #[path = "thread_parker/cloudabi.rs"]
        mod thread_parker;
    } else if #[cfg(all(feature = "i-am-libstd", not(target_arch = "wasm32")))] {
        compile_error!("Not allowed to fall back to generic spin lock based thread parker");
    } else {
        #[path = "thread_parker/generic.rs"]
        mod thread_parker;
    }
}

mod parking_lot;
mod spinwait;
mod util;
mod word_lock;

pub use self::parking_lot::deadlock;
pub use self::parking_lot::{park, unpark_all, unpark_filter, unpark_one, unpark_requeue};
pub use self::parking_lot::{
    FilterOp, ParkResult, ParkToken, RequeueOp, UnparkResult, UnparkToken,
};
pub use self::parking_lot::{DEFAULT_PARK_TOKEN, DEFAULT_UNPARK_TOKEN};
pub use self::spinwait::SpinWait;
