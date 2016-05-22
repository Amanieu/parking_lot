// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use std::thread;
pub use std::sync::{PoisonError, TryLockError, TryLockResult, LockResult};

// Boolean value indicating whether a lock is currently poisoned
pub struct Poison(pub bool);

impl Poison {
    #[inline]
    pub fn map_lock_result<T>(&self, val: T) -> LockResult<T> {
        if self.0 {
            Err(PoisonError::new(val))
        } else {
            Ok(val)
        }
    }
}

// Guard used to detect if a panic occured while a lock was held
pub struct PoisonGuard {
    panicking: bool,
}

impl PoisonGuard {
    // Create a new guard. This records whether the current thread is already
    // unwinding due to a panic.
    #[inline]
    pub fn new() -> PoisonGuard {
        PoisonGuard { panicking: thread::panicking() }
    }

    // Check if a panic occured while a lock was held. If we were already
    // unwinding when we took the lock then we are guaranteed not to have
    // panicked since that would be a double panic and abort the process.
    #[inline]
    pub fn done(&self) -> Poison {
        Poison(!self.panicking && thread::panicking())
    }
}
