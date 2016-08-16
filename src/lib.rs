// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! This library provides implementations of `Mutex`, `RwLock`, `Condvar` and
//! `Once` that are smaller, faster and more flexible than those in the Rust
//! standard library. It also exposes a low-level API for creating your own
//! efficient synchronization primitives.
//!
//! When tested on x86_64 Linux, `parking_lot::Mutex` was found to be 1.5x
//! faster than `std::sync::Mutex` when uncontended, and up to 5x faster when
//! contended from multiple threads. The numbers for `RwLock` vary depending on
//! the number of reader and writer threads, but are almost always faster than
//! the standard library `RwLock`, and even up to 50x faster in some cases.
//!
//! # Features
//!
//! The primitives provided by this library have several advantages over those
//! in the Rust standard library:
//!
//! 1. `Mutex` and `Once` only require 1 byte of storage space, while `Condvar`
//!    and `RwLock` only requires 1 word of storage space. On the other hand the
//!    standard library primitives require a dynamically allocated `Box` to hold
//!    OS-specific synchronization primitives. The small size of `Mutex` in
//!    particular encourages the use of fine-grained locks to increase
//!    parallelism.
//! 2. Since they consist of just a single atomic variable, have constant
//!    initializers and don't need destructors, these primitives can be used as
//!     `static` global variables. The standard library primitives require
//!    dynamic initialization and thus need to be lazily initialized with
//!    `lazy_static!`.
//! 3. Uncontended lock acquisition and release is done through fast inline
//!    paths which only require a single atomic operation.
//! 4. Microcontention (a contended lock with a short critical section) is
//!    efficiently handled by spinning a few times while trying to acquire a
//!    lock.
//! 5. The locks are adaptive and will suspend a thread after a few failed spin
//!    attempts. This makes the locks suitable for both long and short critical
//!    sections.
//! 6. `Condvar`, `RwLock` and `Once` work on Windows XP, unlike the standard
//!    library versions of those types.
//! 7. `RwLock` takes advantage of hardware lock elision on processors that
//!    support it, which can lead to huge performance wins with many readers.
//! 8. `MutexGuard` (and the `RwLock` equivalents) is `Send`, which means it can
//!    be unlocked by a different thread than the one that locked it.
//! 9. `RwLock` will prefer writers, whereas the standard library version makes
//!    no guarantees as to whether readers or writers are given priority.
//! 10. `Condvar` is guaranteed not to produce spurious wakeups. A thread will
//!     only be woken up if it timed out or it was woken up by a notification.
//! 11. `Condvar::notify_all` will only wake up a single thread and requeue the
//!     rest to wait on the associated `Mutex`. This avoids a thundering herd
//!     problem where all threads try to acquire the lock at the same time.
//! 12. `RwLock` supports atomically downgrading a write lock into a read lock.
//! 13. `Mutex` and `RwLock` allow raw unlocking without a RAII guard object.
//! 14. `Mutex<()>` and `RwLock<()>` allow raw locking without a RAII guard
//!     object.
//!
//! # The parking lot
//!
//! To keep these primitives small, all thread queuing and suspending
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
//!                -> bool
//! ```
//!
//! This function performs the following steps:
//!
//! 1. Lock the queue associated with `key`.
//! 2. Call `validate`, if it returns `false`, unlock the queue and return.
//! 3. Add the current thread to the queue.
//! 4. Unlock the queue.
//! 5. Call `before_sleep`.
//! 6. Sleep until we are unparked or `timeout` is reached.
//! 7. If the park timed out, call `timed_out`.
//! 8. Return `true` if we were unparked by another thread, `false` otherwise.
//!
//! ```rust,ignore
//! unsafe fn unpark_one(key: usize,
//!                      callback: FnOnce(UnparkResult))
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
//!                          callback: FnOnce(RequeueOp, usize))
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
//! Building custom synchronization primitives is very simple since
//! `parking_lot` takes care of all the hard parts for you. The most commmon
//! case for a custom primitive would be to integrate a `Mutex` inside another
//! data type. Since a mutex only requires 2 bits, it can share space with other
//! data. For example, one could create an `ArcMutex` type that combines the
//! atomic reference count and the two mutex bits in the same atomic word.

#![warn(missing_docs)]
#![cfg_attr(feature = "nightly", feature(const_fn))]
#![cfg_attr(feature = "nightly", feature(integer_atomics))]
#![cfg_attr(feature = "nightly", feature(asm))]

extern crate smallvec;

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
mod spinwait;
mod word_lock;
mod util;
mod parking_lot;
mod elision;
mod raw_mutex;
mod raw_rwlock;
mod condvar;
mod mutex;
mod rwlock;
mod once;

pub use once::{Once, ONCE_INIT, OnceState};
pub use parking_lot::{UnparkResult, RequeueOp, park, unpark_one, unpark_all, unpark_requeue};
pub use mutex::{Mutex, MutexGuard};
pub use condvar::{Condvar, WaitTimeoutResult};
pub use rwlock::{RwLock, RwLockReadGuard, RwLockWriteGuard};
