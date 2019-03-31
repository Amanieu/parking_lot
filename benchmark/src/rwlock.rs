// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

mod args;
use crate::args::ArgRange;

#[cfg(unix)]
use std::cell::UnsafeCell;
use std::{
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc, Barrier,
    },
    thread,
    time::Duration,
};

trait RwLock<T> {
    fn new(v: T) -> Self;
    fn read<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&T) -> R;
    fn write<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R;
    fn name() -> &'static str;
}

impl<T> RwLock<T> for std::sync::RwLock<T> {
    fn new(v: T) -> Self {
        Self::new(v)
    }
    fn read<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&T) -> R,
    {
        f(&*self.read().unwrap())
    }
    fn write<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        f(&mut *self.write().unwrap())
    }
    fn name() -> &'static str {
        "std::sync::RwLock"
    }
}

impl<T> RwLock<T> for parking_lot::RwLock<T> {
    fn new(v: T) -> Self {
        Self::new(v)
    }
    fn read<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&T) -> R,
    {
        f(&*self.read())
    }
    fn write<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        f(&mut *self.write())
    }
    fn name() -> &'static str {
        "parking_lot::RwLock"
    }
}

impl<T: Copy> RwLock<T> for seqlock::SeqLock<T> {
    fn new(v: T) -> Self {
        Self::new(v)
    }
    fn read<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&T) -> R,
    {
        f(&self.read())
    }
    fn write<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        f(&mut *self.lock_write())
    }
    fn name() -> &'static str {
        "seqlock::SeqLock"
    }
}

#[cfg(not(unix))]
type PthreadRwLock<T> = std::sync::RwLock<T>;

#[cfg(unix)]
struct PthreadRwLock<T>(UnsafeCell<T>, UnsafeCell<libc::pthread_rwlock_t>);
#[cfg(unix)]
unsafe impl<T> Sync for PthreadRwLock<T> {}
#[cfg(unix)]
impl<T> RwLock<T> for PthreadRwLock<T> {
    fn new(v: T) -> Self {
        PthreadRwLock(
            UnsafeCell::new(v),
            UnsafeCell::new(libc::PTHREAD_RWLOCK_INITIALIZER),
        )
    }
    fn read<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&T) -> R,
    {
        unsafe {
            libc::pthread_rwlock_wrlock(self.1.get());
            let res = f(&*self.0.get());
            libc::pthread_rwlock_unlock(self.1.get());
            res
        }
    }
    fn write<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        unsafe {
            libc::pthread_rwlock_wrlock(self.1.get());
            let res = f(&mut *self.0.get());
            libc::pthread_rwlock_unlock(self.1.get());
            res
        }
    }
    fn name() -> &'static str {
        "pthread_rwlock_t"
    }
}
#[cfg(unix)]
impl<T> Drop for PthreadRwLock<T> {
    fn drop(&mut self) {
        unsafe {
            libc::pthread_rwlock_destroy(self.1.get());
        }
    }
}

fn run_benchmark<M: RwLock<f64> + Send + Sync + 'static>(
    num_writer_threads: usize,
    num_reader_threads: usize,
    work_per_critical_section: usize,
    work_between_critical_sections: usize,
    seconds_per_test: usize,
) -> (Vec<usize>, Vec<usize>) {
    let lock = Arc::new(([0u8; 300], M::new(0.0), [0u8; 300]));
    let keep_going = Arc::new(AtomicBool::new(true));
    let barrier = Arc::new(Barrier::new(num_reader_threads + num_writer_threads));
    let mut writers = vec![];
    let mut readers = vec![];
    for _ in 0..num_writer_threads {
        let barrier = barrier.clone();
        let lock = lock.clone();
        let keep_going = keep_going.clone();
        writers.push(thread::spawn(move || {
            let mut local_value = 0.0;
            let mut value = 0.0;
            let mut iterations = 0usize;
            barrier.wait();
            while keep_going.load(Ordering::Relaxed) {
                lock.1.write(|shared_value| {
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
    for _ in 0..num_reader_threads {
        let barrier = barrier.clone();
        let lock = lock.clone();
        let keep_going = keep_going.clone();
        readers.push(thread::spawn(move || {
            let mut local_value = 0.0;
            let mut value = 0.0;
            let mut iterations = 0usize;
            barrier.wait();
            while keep_going.load(Ordering::Relaxed) {
                lock.1.read(|shared_value| {
                    for _ in 0..work_per_critical_section {
                        local_value += value;
                        local_value *= *shared_value;
                        value = local_value;
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

    thread::sleep(Duration::new(seconds_per_test as u64, 0));
    keep_going.store(false, Ordering::Relaxed);

    let run_writers = writers
        .into_iter()
        .map(|x| x.join().unwrap().0)
        .collect::<Vec<usize>>();
    let run_readers = readers
        .into_iter()
        .map(|x| x.join().unwrap().0)
        .collect::<Vec<usize>>();

    (run_writers, run_readers)
}

fn run_benchmark_iterations<M: RwLock<f64> + Send + Sync + 'static>(
    num_writer_threads: usize,
    num_reader_threads: usize,
    work_per_critical_section: usize,
    work_between_critical_sections: usize,
    seconds_per_test: usize,
    test_iterations: usize,
) {
    let mut writers = vec![];
    let mut readers = vec![];

    for _ in 0..test_iterations {
        let (run_writers, run_readers) = run_benchmark::<M>(
            num_writer_threads,
            num_reader_threads,
            work_per_critical_section,
            work_between_critical_sections,
            seconds_per_test,
        );
        writers.extend_from_slice(&run_writers);
        readers.extend_from_slice(&run_readers);
    }

    let total_writers = writers.iter().fold(0f64, |a, b| a + *b as f64) / test_iterations as f64;
    let total_readers = readers.iter().fold(0f64, |a, b| a + *b as f64) / test_iterations as f64;
    println!(
        "{:20} - [write] {:10.3} kHz [read] {:10.3} kHz",
        M::name(),
        total_writers as f64 / seconds_per_test as f64 / 1000.0,
        total_readers as f64 / seconds_per_test as f64 / 1000.0
    );
}

fn run_all(
    args: &[ArgRange],
    first: &mut bool,
    num_writer_threads: usize,
    num_reader_threads: usize,
    work_per_critical_section: usize,
    work_between_critical_sections: usize,
    seconds_per_test: usize,
    test_iterations: usize,
) {
    if num_writer_threads == 0 && num_reader_threads == 0 {
        return;
    }
    if *first || !args[0].is_single() || !args[1].is_single() {
        println!(
            "- Running with {} writer threads and {} reader threads",
            num_writer_threads, num_reader_threads
        );
    }
    if *first || !args[2].is_single() || !args[3].is_single() {
        println!(
            "- {} iterations inside lock, {} iterations outside lock",
            work_per_critical_section, work_between_critical_sections
        );
    }
    if *first || !args[4].is_single() {
        println!("- {} seconds per test", seconds_per_test);
    }
    *first = false;

    run_benchmark_iterations::<parking_lot::RwLock<f64>>(
        num_writer_threads,
        num_reader_threads,
        work_per_critical_section,
        work_between_critical_sections,
        seconds_per_test,
        test_iterations,
    );
    run_benchmark_iterations::<seqlock::SeqLock<f64>>(
        num_writer_threads,
        num_reader_threads,
        work_per_critical_section,
        work_between_critical_sections,
        seconds_per_test,
        test_iterations,
    );
    run_benchmark_iterations::<std::sync::RwLock<f64>>(
        num_writer_threads,
        num_reader_threads,
        work_per_critical_section,
        work_between_critical_sections,
        seconds_per_test,
        test_iterations,
    );
    if cfg!(unix) {
        run_benchmark_iterations::<PthreadRwLock<f64>>(
            num_writer_threads,
            num_reader_threads,
            work_per_critical_section,
            work_between_critical_sections,
            seconds_per_test,
            test_iterations,
        );
    }
}
fn main() {
    let args = args::parse(&[
        "numWriterThreads",
        "numReaderThreads",
        "workPerCriticalSection",
        "workBetweenCriticalSections",
        "secondsPerTest",
        "testIterations",
    ]);
    let mut first = true;
    for num_writer_threads in args[0] {
        for num_reader_threads in args[1] {
            for work_per_critical_section in args[2] {
                for work_between_critical_sections in args[3] {
                    for seconds_per_test in args[4] {
                        for test_iterations in args[5] {
                            run_all(
                                &args,
                                &mut first,
                                num_writer_threads,
                                num_reader_threads,
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
}
