// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

extern crate parking_lot;
extern crate libc;

mod args;
use args::ArgRange;

use std::thread;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;
use std::cell::UnsafeCell;

trait Mutex<T> {
    fn new(v: T) -> Self;
    fn lock<F, R>(&self, f: F) -> R where F: FnOnce(&mut T) -> R;
    fn name() -> &'static str;
}

impl<T> Mutex<T> for std::sync::Mutex<T> {
    fn new(v: T) -> Self {
        Self::new(v)
    }
    fn lock<F, R>(&self, f: F) -> R
        where F: FnOnce(&mut T) -> R
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
        where F: FnOnce(&mut T) -> R
    {
        f(&mut *self.lock())
    }
    fn name() -> &'static str {
        "parking_lot::Mutex"
    }
}

struct PthreadMutex<T>(UnsafeCell<T>, libc::pthread_mutex_t);
unsafe impl<T> Sync for PthreadMutex<T> {}
impl<T> Mutex<T> for PthreadMutex<T> {
    fn new(v: T) -> Self {
        PthreadMutex(UnsafeCell::new(v), libc::PTHREAD_MUTEX_INITIALIZER)
    }
    fn lock<F, R>(&self, f: F) -> R
        where F: FnOnce(&mut T) -> R
    {
        unsafe {
            libc::pthread_mutex_lock(&self.1 as *const _ as *mut _);
            let res = f(&mut *self.0.get());
            libc::pthread_mutex_unlock(&self.1 as *const _ as *mut _);
            res
        }
    }
    fn name() -> &'static str {
        "pthread_mutex_t"
    }
}

fn run_benchmark<M: Mutex<f64> + Send + Sync + 'static>(num_threads: usize,
                                                        work_per_critical_section: usize,
                                                        work_between_critical_sections: usize,
                                                        seconds_per_test: usize) {
    let lock = Arc::new(([0u8; 300], M::new(0.0), [0u8; 300]));
    let keep_going = Arc::new(AtomicBool::new(true));
    let mut threads = vec![];
    for _ in 0..num_threads {
        let lock = lock.clone();
        let keep_going = keep_going.clone();
        threads.push(thread::spawn(move || {
            let mut local_value = 0.0;
            let mut value = 0.0;
            let mut iterations = 0usize;
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
            iterations
        }));
    }

    thread::sleep(Duration::new(seconds_per_test as u64, 0));
    keep_going.store(false, Ordering::Relaxed);

    let total = threads.into_iter().map(|x| x.join().unwrap()).fold(0, |a, b| a + b);
    println!("{:20} - {:10.3} kHz",
             M::name(),
             total as f64 / seconds_per_test as f64 / 1000.0);
}

fn run_all(args: &[ArgRange],
           first: &mut bool,
           num_threads: usize,
           work_per_critical_section: usize,
           work_between_critical_sections: usize,
           seconds_per_test: usize) {
    if num_threads == 0 {
        return;
    }
    if *first || !args[0].is_single() {
        println!("- Running with {} threads", num_threads);
    }
    if *first || !args[1].is_single() || !args[2].is_single() {
        println!("- {} iterations inside lock, {} iterations outside lock",
                 work_per_critical_section,
                 work_between_critical_sections);
    }
    if *first || !args[3].is_single() {
        println!("- {} seconds per test", seconds_per_test);
    }
    *first = false;

    run_benchmark::<parking_lot::Mutex<f64>>(num_threads,
                                             work_per_critical_section,
                                             work_between_critical_sections,
                                             seconds_per_test);
    run_benchmark::<std::sync::Mutex<f64>>(num_threads,
                                           work_per_critical_section,
                                           work_between_critical_sections,
                                           seconds_per_test);
    run_benchmark::<PthreadMutex<f64>>(num_threads,
                                       work_per_critical_section,
                                       work_between_critical_sections,
                                       seconds_per_test);
}

fn main() {
    let args = args::parse(&["numThreads",
                             "workPerCriticalSection",
                             "workBetweenCriticalSections",
                             "secondsPerTest"]);
    let mut first = true;
    for num_threads in args[0] {
        for work_per_critical_section in args[1] {
            for work_between_critical_sections in args[2] {
                for seconds_per_test in args[3] {
                    run_all(&args,
                            &mut first,
                            num_threads,
                            work_per_critical_section,
                            work_between_critical_sections,
                            seconds_per_test);
                }
            }
        }
    }
}
