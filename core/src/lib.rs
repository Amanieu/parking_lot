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
//! functionality is offloaded to the *parking lot*. The idea behind this is
//! based on the Webkit [`WTF::ParkingLot`]
//! (https://webkit.org/blog/6161/locking-in-webkit/) class, which essentially
//! consists of a hash table mapping of lock addresses to queues of parked
//! (sleeping) threads. The Webkit parking lot was itself inspired by Linux
//! [futexes](http://man7.org/linux/man-pages/man2/futex.2.html), but it is more
//! powerful since it allows invoking callbacks while holding a queue lock.
//!
//! *Parking* refers to suspending the thread while simultaneously enqueuing it
//! on a queue keyed by some address. *Unparking* refers to dequeuing a thread
//! from a queue keyed by some address and resuming it. The parking lot API
//! consists of just 4 functions:
//!
//! ```rust,ignore
//! unsafe fn park(key: usize,
//!                validate: FnOnce() -> bool,
//!                before_sleep: FnOnce(),
//!                timed_out: FnOnce(usize, UnparkResult),
//!                timeout: Option<Instant>)
//!                -> Option<UnparkToken>
//! ```
//!
//! This function performs the following steps:
//!
//! 1. Lock the queue associated with `key`.
//! 2. Call `validate`, if it returns `None`, unlock the queue and return.
//! 3. Add the current thread to the queue.
//! 4. Unlock the queue.
//! 5. Call `before_sleep`.
//! 6. Sleep until we are unparked or `timeout` is reached.
//! 7. If the park timed out, call `timed_out` and then return `None`.
//! 8. Return an `UnparkToken` if we were unparked by another thread.
//!
//! ```rust,ignore
//! unsafe fn unpark_one(key: usize,
//!                      callback: FnOnce(UnparkResult) -> UnparkToken)
//!                      -> UnparkResult
//! ```
//!
//! This function will unpark a single thread from the queue associated with
//! `key`. The `callback` function is invoked while holding the queue lock but
//! before the thread is unparked. The `UnparkResult` indicates whether the
//! queue was empty and, if not, whether there are still threads remaining in
//! the queue.
//!
//! ```rust,ignore
//! unsafe fn unpark_all(key: usize) -> usize
//! ```
//!
//! This function will unpark all threads in the queue associated with `key`. It
//! returns the number of threads that were unparked.
//!
//! ```rust,ignore
//! unsafe fn unpark_requeue(key_from: usize,
//!                          key_to: usize,
//!                          validate: FnOnce() -> RequeueOp,
//!                          callback: FnOnce(RequeueOp, usize) -> UnparkToken)
//!                          -> usize
//! ```
//!
//! This function will remove all threads from the queue associated with
//! `key_from`, optionally unpark the first one and move the rest to the queue
//! associated with `key_to`. The `validate` function is invoked while holding
//! both queue locks and can choose whether to abort the operation and whether
//! to unpark one thread from the queue. The `callback` function is then called
//! with the result of `validate` and the number of threads that were in the
//! original queue.
//!
//! # Building custom synchronization primitives
//!
//! Building custom synchronization primitives is very simple since the parking
//! lot takes care of all the hard parts for you. The most commmon case
//! for a custom primitive would be to integrate a `Mutex` inside another
//! data type. Since a mutex only requires 2 bits, it can share space with other
//! data. For example, one could create an `ArcMutex` type that combines the
//! atomic reference count and the two mutex bits in the same atomic word.

#![warn(missing_docs)]
#![cfg_attr(feature = "nightly", feature(const_fn))]
#![cfg_attr(feature = "nightly", feature(integer_atomics))]
#![cfg_attr(feature = "nightly", feature(asm))]

extern crate smallvec;
extern crate rand;

#[cfg(unix)]
extern crate libc;

#[cfg(windows)]
extern crate winapi;
#[cfg(windows)]
extern crate kernel32;

#[cfg(all(feature = "nightly", target_os = "linux"))]
#[path = "thread_parker/linux.rs"]
mod thread_parker;
#[cfg(all(unix, not(all(feature = "nightly", target_os = "linux"))))]
#[path = "thread_parker/unix.rs"]
mod thread_parker;
#[cfg(windows)]
#[path = "thread_parker/windows.rs"]
mod thread_parker;
#[cfg(not(any(windows, unix)))]
#[path = "thread_parker/generic.rs"]
mod thread_parker;

#[cfg(not(feature = "nightly"))]
mod stable;

mod util;
mod spinwait;
mod word_lock;
mod parking_lot;

pub use parking_lot::{UnparkResult, RequeueOp, UnparkToken, DEFAULT_UNPARK_TOKEN};
pub use parking_lot::{park, unpark_one, unpark_all, unpark_requeue};
pub use spinwait::SpinWait;
