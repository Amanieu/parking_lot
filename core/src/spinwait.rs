// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::thread_parker;
use core::{hint::spin_loop, time::Duration};
use std::thread;

// Wastes some CPU time for the given number of iterations,
// using a hint to indicate to the CPU that we are spinning.
#[inline]
fn cpu_relax(iterations: u32) {
    for _ in 0..iterations {
        spin_loop()
    }
}

/// A counter used to perform exponential backoff in spin loops.
#[derive(Default)]
pub struct SpinWait {
    counter: u32,
}

impl SpinWait {
    /// Creates a new `SpinWait`.
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    /// Resets a `SpinWait` to its initial state.
    #[inline]
    pub fn reset(&mut self) {
        self.counter = 0;
    }

    /// Spins until the sleep threshold has been reached.
    ///
    /// This function returns `false` if the sleep threshold has been reached,
    /// at which point further spinning has diminishing returns and the thread
    /// should be parked instead.
    ///
    /// The spin strategy will initially use a CPU-bound loop but will fall back
    /// to yielding the CPU to the OS after a few iterations.
    /// Before parking, 'spin()' will finally try sleep 1ms, 4 times to avoid
    /// entering parking too frequently in case of cache contention.
    #[inline]
    pub fn spin(&mut self) -> bool {
        if self.counter >= 15 {
            return false;
        }
        self.counter += 1;
        if self.counter <= 3 {
            cpu_relax(1 << self.counter);
        } else if self.counter <= 10 {
            thread_parker::thread_yield();
        } else {
            thread::sleep(Duration::from_millis(1));
        }
        true
    }

    /// Spins without yielding the thread to the OS.
    ///
    /// Instead, the backoff is simply capped at a maximum value. This can be
    /// used to improve throughput in `compare_exchange` loops that have high
    /// contention.
    #[inline]
    pub fn spin_no_yield(&mut self) {
        self.counter += 1;
        if self.counter > 10 {
            self.counter = 10;
        }
        cpu_relax(1 << self.counter);
    }
}
