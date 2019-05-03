// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use std::time::{Duration, Instant};

// Option::unchecked_unwrap
pub trait UncheckedOptionExt<T> {
    unsafe fn unchecked_unwrap(self) -> T;
}

impl<T> UncheckedOptionExt<T> for Option<T> {
    #[inline]
    unsafe fn unchecked_unwrap(self) -> T {
        match self {
            Some(x) => x,
            None => unreachable(),
        }
    }
}

// Equivalent to intrinsics::unreachable() in release mode
#[inline]
unsafe fn unreachable() -> ! {
    if cfg!(debug_assertions) {
        unreachable!();
    } else {
        enum Void {}
        match *(1 as *const Void) {}
    }
}

#[inline]
pub fn to_deadline(timeout: Duration) -> Option<Instant> {
    #[cfg(any(has_checked_instant, feature = "i-am-libstd"))]
    let deadline = Instant::now().checked_add(timeout);
    #[cfg(not(any(has_checked_instant, feature = "i-am-libstd")))]
    let deadline = Some(Instant::now() + timeout);

    deadline
}
