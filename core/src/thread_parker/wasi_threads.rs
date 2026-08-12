// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! Thread parker for threaded wasi targets (wasm32-wasip1-threads etc),
//! built on std's Mutex/Condvar which are futex-based there. Used on stable,
//! where the wasm_atomic parker isn't available because its intrinsics are
//! still unstable (rust-lang/rust#77839). Without this, threaded wasi builds
//! on stable fall through to the panicking wasm.rs stub.

use core::mem;
use std::sync::{Condvar, Mutex, MutexGuard};
use std::time::Instant;

// Helper type for putting a thread to sleep until some other thread wakes it up
pub struct ThreadParker {
    should_park: Mutex<bool>,
    condvar: Condvar,
}

impl super::ThreadParkerT for ThreadParker {
    type UnparkHandle = UnparkHandle;

    const IS_CHEAP_TO_CONSTRUCT: bool = true;

    #[inline]
    fn new() -> ThreadParker {
        ThreadParker {
            should_park: Mutex::new(false),
            condvar: Condvar::new(),
        }
    }

    #[inline]
    unsafe fn prepare_park(&self) {
        *self.should_park.lock().unwrap() = true;
    }

    #[inline]
    unsafe fn timed_out(&self) -> bool {
        *self.should_park.lock().unwrap()
    }

    #[inline]
    unsafe fn park(&self) {
        let mut should_park = self.should_park.lock().unwrap();
        while *should_park {
            should_park = self.condvar.wait(should_park).unwrap();
        }
    }

    #[inline]
    unsafe fn park_until(&self, timeout: Instant) -> bool {
        let mut should_park = self.should_park.lock().unwrap();
        while *should_park {
            let now = Instant::now();
            if now >= timeout {
                return false;
            }
            let (guard, _) = self
                .condvar
                .wait_timeout(should_park, timeout - now)
                .unwrap();
            should_park = guard;
        }
        true
    }

    #[inline]
    unsafe fn unpark_lock(&self) -> UnparkHandle {
        let guard = self.should_park.lock().unwrap();
        UnparkHandle {
            // The lifetime is extended so the guard can live in the handle
            // until unpark() runs. Holding the mutex keeps the parked thread
            // alive until then, so the parker can't go away under us (the
            // other parkers do the same thing with raw pointers).
            guard: mem::transmute::<MutexGuard<'_, bool>, MutexGuard<'static, bool>>(guard),
            condvar: &self.condvar,
        }
    }
}

pub struct UnparkHandle {
    guard: MutexGuard<'static, bool>,
    condvar: *const Condvar,
}

impl super::UnparkHandleT for UnparkHandle {
    #[inline]
    unsafe fn unpark(mut self) {
        *self.guard = false;

        // We notify while holding the lock here to avoid races with the target
        // thread. In particular, the thread could exit after we release the
        // mutex, which would make the condvar access invalid memory.
        (*self.condvar).notify_one();
        drop(self.guard);
    }
}

#[inline]
pub fn thread_yield() {
    std::thread::yield_now();
}
