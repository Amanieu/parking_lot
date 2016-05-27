// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

#[cfg(windows)]
use kernel32;
#[cfg(unix)]
use libc;
#[cfg(not(any(windows, unix)))]
use std::thread;
#[cfg(not(feature = "nightly"))]
use std::sync::atomic::{Ordering, fence};

// Yields the rest of the current timeslice to the OS
#[cfg(windows)]
fn thread_yield() {
    unsafe {
        // We don't use SwitchToThread here because it doesn't consider all
        // threads in the system and the thread we are waiting for may not get
        // selected.
        kernel32::Sleep(0);
    }
}
#[cfg(unix)]
fn thread_yield() {
    unsafe {
        libc::sched_yield();
    }
}
#[cfg(not(any(windows, unix)))]
fn thread_yield() {
    thread::yield_now();
}

// Wastes some CPU time for the given number of iterations, preferably also
// using a hint to indicate to the CPU that we are spinning.
#[cfg(all(feature = "nightly", any(target_arch = "x86", target_arch = "x86_64")))]
fn cpu_relax(iterations: u32) {
    for _ in 0..iterations {
        unsafe {
            asm!("pause" ::: "memory" : "volatile");
        }
    }
}
#[cfg(all(feature = "nightly", target_arch = "aarch64"))]
fn cpu_relax(iterations: u32) {
    for _ in 0..iterations {
        unsafe {
            asm!("yield" ::: "memory" : "volatile");
        }
    }
}
#[cfg(all(feature = "nightly", not(any(target_arch = "x86",
                                       target_arch = "x86_64",
                                       target_arch = "aarch64"))))]
fn cpu_relax(iterations: u32) {
    for _ in 0..iterations {
        unsafe {
            asm!("" ::: "memory" : "volatile");
        }
    }
}
#[cfg(not(feature = "nightly"))]
fn cpu_relax(iterations: u32) {
    // This is a bit tricky: we rely on the fact that LLVM doesn't optimize
    // atomic operations and effectively treats them as volatile.
    for _ in 0..iterations {
        fence(Ordering::SeqCst);
    }
}

// Counter used for adaptive spinning
pub struct SpinWait {
    counter: u32,
}

impl SpinWait {
    pub fn new() -> SpinWait {
        SpinWait { counter: 0 }
    }

    pub fn reset(&mut self) {
        self.counter = 0;
    }

    // Adaptive spinning: we start off by calling cpu_relax with increasing
    // iteration counts, after which we fall back to thread_yield. After
    // yielding a few times, we give up and return false, indicating the thread
    // should be parked.
    pub fn spin(&mut self) -> bool {
        if self.counter >= 20 {
            return false;
        }
        self.counter += 1;
        if self.counter <= 10 {
            cpu_relax(4 << self.counter);
        } else {
            thread_yield();
        }
        true
    }

    // Spin without yielding. We just cap the maximum spinning time. This is
    // useful for compare_exchange loops that have high contention.
    pub fn spin_no_yield(&mut self) {
        self.counter += 1;
        if self.counter > 10 {
            self.counter = 10;
        }
        cpu_relax(4 << self.counter);
    }
}
