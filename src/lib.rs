//! This library provides compact and efficient implementations of `Mutex`,
//! `RwLock`, `RecursiveRwLock`, `Condvar` and `Once`. It also provides a
//! `ReentrantMutex` type.

#![warn(missing_docs)]
#![warn(rust_2018_idioms)]

mod condvar;
mod fair_mutex;
mod mutex;
mod once;
mod raw_condvar;
mod raw_fair_mutex;
mod raw_mutex;
mod raw_rwlock;
mod recursive_rwlock;
mod remutex;
mod rwlock;
mod util;

#[cfg(feature = "deadlock_detection")]
pub mod deadlock;
#[cfg(not(feature = "deadlock_detection"))]
mod deadlock;

// If deadlock detection is enabled, we cannot allow lock guards to be sent to
// other threads.
#[cfg(all(feature = "send_guard", feature = "deadlock_detection"))]
compile_error!("the `send_guard` and `deadlock_detection` features cannot be used together");
#[cfg(feature = "send_guard")]
type GuardMarker = lock_api::GuardSend;
#[cfg(not(feature = "send_guard"))]
type GuardMarker = lock_api::GuardNoSend;

pub use self::condvar::{Condvar, WaitTimeoutResult};
pub use self::fair_mutex::{FairMutex, FairMutexGuard, MappedFairMutexGuard, const_fair_mutex};
pub use self::mutex::{MappedMutexGuard, Mutex, MutexGuard, const_mutex};
pub use self::once::{Once, OnceState};
pub use self::raw_condvar::RawCondvar;
pub use self::raw_fair_mutex::RawFairMutex;
pub use self::raw_mutex::RawMutex;
pub use self::raw_rwlock::{RawRwLock, RawRwLockRecursive};
pub use self::recursive_rwlock::{
    MappedRecursiveRwLockReadGuard, MappedRecursiveRwLockWriteGuard, RecursiveRwLock,
    RecursiveRwLockReadGuard, RecursiveRwLockUpgradableReadGuard, RecursiveRwLockWriteGuard,
};
pub use self::remutex::{
    MappedReentrantMutexGuard, RawThreadId, ReentrantMutex, ReentrantMutexGuard,
    const_reentrant_mutex,
};
pub use self::rwlock::{
    MappedRwLockReadGuard, MappedRwLockWriteGuard, RwLock, RwLockReadGuard,
    RwLockUpgradableReadGuard, RwLockWriteGuard, const_rwlock,
};
pub use ::lock_api;

#[cfg(feature = "arc_lock")]
pub use self::lock_api::{
    ArcMutexGuard, ArcReentrantMutexGuard, ArcRwLockReadGuard, ArcRwLockUpgradableReadGuard,
    ArcRwLockWriteGuard,
};
