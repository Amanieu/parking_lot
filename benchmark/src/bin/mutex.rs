// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use parking_lot_benchmark::args;
use parking_lot_benchmark::args::ArgRange;

#[cfg(any(windows, unix))]
use std::cell::UnsafeCell;
use std::{
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc, Barrier,
    },
    thread,
    time::Duration,
};

trait Mutex<T> {
    fn new(v: T) -> Self;
    fn lock<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R;
    fn name() -> &'static str;
}

impl<T> Mutex<T> for std::sync::Mutex<T> {
    fn new(v: T) -> Self {
        Self::new(v)
    }
    fn lock<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        f(&mut *self.lock().unwrap())
    }
    fn name() -> &'static str {
        "std::sync::Mutex"
    }
}

impl<T> Mutex<T> for parking_lot::Mutex<T> {
    fn new(v: T) -> Self {
        Self::new(v)
    }
    fn lock<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        f(&mut *self.lock())
    }
    fn name() -> &'static str {
        "parking_lot::Mutex"
    }
}

#[cfg(not(windows))]
type SrwLock<T> = std::sync::Mutex<T>;

#[cfg(windows)]
use winapi::um::synchapi;
#[cfg(windows)]
struct SrwLock<T>(UnsafeCell<T>, UnsafeCell<synchapi::SRWLOCK>);
#[cfg(windows)]
unsafe impl<T> Sync for SrwLock<T> {}
#[cfg(windows)]
unsafe impl<T: Send> Send for SrwLock<T> {}
#[cfg(windows)]
impl<T> Mutex<T> for SrwLock<T> {
    fn new(v: T) -> Self {
        let mut h: synchapi::SRWLOCK = synchapi::SRWLOCK { Ptr: std::ptr::null_mut() };

        unsafe {
            synchapi::InitializeSRWLock(&mut h);
        }
        SrwLock(
            UnsafeCell::new(v),
            UnsafeCell::new(h),
        )
    }
    fn lock<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        unsafe {
            synchapi::AcquireSRWLockExclusive(self.1.get());
            let res = f(&mut *self.0.get());
            synchapi::ReleaseSRWLockExclusive(self.1.get());
            res
        }
    }
    fn name() -> &'static str {
        "winapi_srwlock"
    }
}

#[cfg(not(unix))]
type PthreadMutex<T> = std::sync::Mutex<T>;

#[cfg(unix)]
struct PthreadMutex<T>(UnsafeCell<T>, UnsafeCell<libc::pthread_mutex_t>);
#[cfg(unix)]
unsafe impl<T> Sync for PthreadMutex<T> {}
#[cfg(unix)]
impl<T> Mutex<T> for PthreadMutex<T> {
    fn new(v: T) -> Self {
        PthreadMutex(
            UnsafeCell::new(v),
            UnsafeCell::new(libc::PTHREAD_MUTEX_INITIALIZER),
        )
    }
    fn lock<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        unsafe {
            libc::pthread_mutex_lock(self.1.get());
            let res = f(&mut *self.0.get());
            libc::pthread_mutex_unlock(self.1.get());
            res
        }
    }
    fn name() -> &'static str {
        "pthread_mutex_t"
    }
}
#[cfg(unix)]
impl<T> Drop for PthreadMutex<T> {
    fn drop(&mut self) {
        unsafe {
            libc::pthread_mutex_destroy(self.1.get());
        }
    }
}

fn run_benchmark<M: Mutex<f64> + Send + Sync + 'static>(
    num_threads: usize,
    work_per_critical_section: usize,
    work_between_critical_sections: usize,
    seconds_per_test: usize,
) -> Vec<usize> {
    let lock = Arc::new(([0u8; 300], M::new(0.0), [0u8; 300]));
    let keep_going = Arc::new(AtomicBool::new(true));
    let barrier = Arc::new(Barrier::new(num_threads));
    let mut threads = vec![];
    for _ in 0..num_threads {
        let barrier = barrier.clone();
        let lock = lock.clone();
        let keep_going = keep_going.clone();
        threads.push(thread::spawn(move || {
            let mut local_value = 0.0;
            let mut value = 0.0;
            let mut iterations = 0usize;
            barrier.wait();
            while keep_going.load(Ordering::Relaxed) {
                lock.1.lock(|shared_value| {
                    for _ in 0..work_per_critical_section {
                        *shared_value += value;
                        *shared_value *= 1.01;
                        value = *shared_value;
                    }
                });
                for _ in 0..work_between_critical_sections {
                    local_value += value;
                    local_value *= 1.01;
                    value = local_value;
                }
                iterations += 1;
            }
            (iterations, value)
        }));
    }

    thread::sleep(Duration::from_secs(seconds_per_test as u64));
    keep_going.store(false, Ordering::Relaxed);
    threads.into_iter().map(|x| x.join().unwrap().0).collect()
}

fn run_benchmark_iterations<M: Mutex<f64> + Send + Sync + 'static>(
    num_threads: usize,
    work_per_critical_section: usize,
    work_between_critical_sections: usize,
    seconds_per_test: usize,
    test_iterations: usize,
) {
    let mut data = vec![];
    for _ in 0..test_iterations {
        let run_data = run_benchmark::<M>(
            num_threads,
            work_per_critical_section,
            work_between_critical_sections,
            seconds_per_test,
        );
        data.extend_from_slice(&run_data);
    }

    let average = data.iter().fold(0f64, |a, b| a + *b as f64) / data.len() as f64;
    let variance = data
        .iter()
        .fold(0f64, |a, b| a + ((*b as f64 - average).powi(2)))
        / data.len() as f64;
    data.sort();

    let k_hz = 1.0 / seconds_per_test as f64 / 1000.0;
    println!(
        "{:20} | {:10.3} kHz | {:10.3} kHz | {:10.3} kHz",
        M::name(),
        average * k_hz,
        data[data.len() / 2] as f64 * k_hz,
        variance.sqrt() * k_hz
    );
}

fn run_all(
    args: &[ArgRange],
    first: &mut bool,
    num_threads: usize,
    work_per_critical_section: usize,
    work_between_critical_sections: usize,
    seconds_per_test: usize,
    test_iterations: usize,
) {
    if num_threads == 0 {
        return;
    }
    if *first || !args[0].is_single() {
        println!("- Running with {num_threads} threads");
    }
    if *first || !args[1].is_single() || !args[2].is_single() {
        println!(
            "- {work_per_critical_section} iterations inside lock, {work_between_critical_sections} iterations outside lock"
        );
    }
    if *first || !args[3].is_single() {
        println!("- {seconds_per_test} seconds per test");
    }
    *first = false;

    println!(
        "{:^20} | {:^14} | {:^14} | {:^14}",
        "name", "average", "median", "std.dev."
    );

    run_benchmark_iterations::<parking_lot::Mutex<f64>>(
        num_threads,
        work_per_critical_section,
        work_between_critical_sections,
        seconds_per_test,
        test_iterations,
    );

    run_benchmark_iterations::<std::sync::Mutex<f64>>(
        num_threads,
        work_per_critical_section,
        work_between_critical_sections,
        seconds_per_test,
        test_iterations,
    );
    if cfg!(windows) {
        run_benchmark_iterations::<SrwLock<f64>>(
            num_threads,
            work_per_critical_section,
            work_between_critical_sections,
            seconds_per_test,
            test_iterations,
        );
    }
    if cfg!(unix) {
        run_benchmark_iterations::<PthreadMutex<f64>>(
            num_threads,
            work_per_critical_section,
            work_between_critical_sections,
            seconds_per_test,
            test_iterations,
        );
    }
}

fn main() {
    let args = args::parse(&[
        "numThreads",
        "workPerCriticalSection",
        "workBetweenCriticalSections",
        "secondsPerTest",
        "testIterations",
    ]);
    let mut first = true;
    for num_threads in args[0] {
        for work_per_critical_section in args[1] {
            for work_between_critical_sections in args[2] {
                for seconds_per_test in args[3] {
                    for test_iterations in args[4] {
                        run_all(
                            &args,
                            &mut first,
                            num_threads,
                            work_per_critical_section,
                            work_between_critical_sections,
                            seconds_per_test,
                            test_iterations,
                        );
                    }
                }
            }
        }
    }
}
