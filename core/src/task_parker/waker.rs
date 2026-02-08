// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! A simple Context/Waker based task parker.

use crate::thread_parker::UnparkHandleT;
use crate::util::{waker, ImmediateFuture};
use core::sync::atomic::{AtomicBool, Ordering};
use std::collections::BinaryHeap;
use std::sync::mpsc::{channel, Receiver, Sender};
use std::sync::LazyLock;
use std::task::{Context, Poll, Waker};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

// Helper type for putting a task to sleep until some other thread/task wakes it up
pub struct TaskParker {
    parked: AtomicBool,
    wake_scheduled: AtomicBool,
    waker: Waker,
}

impl super::TaskParkerT for TaskParker {
    type Context<'a> = Context<'a>;
    type UnparkHandle = UnparkHandle;

    #[inline]
    fn new(cx: &mut Context<'_>) -> TaskParker {
        TaskParker {
            parked: AtomicBool::new(false),
            wake_scheduled: AtomicBool::new(true),
            waker: waker().poll_ready(cx),
        }
    }

    #[inline]
    fn is_valid_context(&self, cx: &mut Context<'_>) -> bool {
        self.waker.will_wake(cx.waker())
    }

    #[inline]
    unsafe fn prepare_park(&self, cx: &mut Context<'_>) {
        debug_assert!(
            self.is_valid_context(cx),
            "Called TaskParker::prepare_park with unrelated context."
        );
        self.parked.store(true, Ordering::Relaxed);
        self.wake_scheduled.store(false, Ordering::Relaxed);
    }

    #[inline]
    unsafe fn timed_out(&self, cx: &mut Context<'_>) -> bool {
        debug_assert!(
            self.is_valid_context(cx),
            "Called TaskParker::timed_out with unrelated context."
        );
        self.parked.load(Ordering::Relaxed)
    }

    #[inline]
    unsafe fn park(&self, cx: &mut Context<'_>) -> Poll<()> {
        debug_assert!(
            self.is_valid_context(cx),
            "Called TaskParker::park with unrelated context."
        );
        if self.parked.load(Ordering::Acquire) {
            Poll::Pending
        } else {
            Poll::Ready(())
        }
    }

    #[inline]
    unsafe fn park_until(&self, cx: &mut Context<'_>, timeout: Instant) -> Poll<bool> {
        debug_assert!(
            self.is_valid_context(cx),
            "Called TaskParker::park_until with unrelated context."
        );
        match self.park(cx) {
            Poll::Ready(()) => Poll::Ready(true),
            Poll::Pending if Instant::now() >= timeout => Poll::Ready(false),
            Poll::Pending => {
                if !self.wake_scheduled.swap(true, Ordering::Acquire) {
                    schedule_wake(timeout, self.waker.clone());
                } else {
                    debug_assert!(
                        false,
                        "TaskParker::park_until was called again prematurely."
                    );
                }
                Poll::Pending
            }
        }
    }

    #[inline]
    unsafe fn unpark_lock(&self) -> UnparkHandle {
        // We don't need to lock anything, just clear the state
        self.parked.store(false, Ordering::Release);
        self.wake_scheduled.store(true, Ordering::Release);
        UnparkHandle(self.waker.clone())
    }
}

pub struct UnparkHandle(Waker);
impl UnparkHandleT for UnparkHandle {
    #[inline]
    unsafe fn unpark(self) {
        self.0.wake();
    }
}

fn schedule_wake(instant: Instant, waker: Waker) {
    let (tx, rooster) = &*ROOSTER;
    tx.send(Sleeper {
        until: instant,
        waker,
    })
    .unwrap();
    rooster.thread().unpark();
}
#[derive(Debug)]
struct Sleeper {
    until: Instant,
    waker: Waker,
}
impl PartialEq for Sleeper {
    fn eq(&self, other: &Self) -> bool {
        self.until == other.until
    }
}
impl Eq for Sleeper {}
impl PartialOrd for Sleeper {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        other.until.partial_cmp(&self.until)
    }
}
impl Ord for Sleeper {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other.until.cmp(&self.until)
    }
}
static ROOSTER: LazyLock<(Sender<Sleeper>, JoinHandle<()>)> = LazyLock::new(|| {
    let (tx, rx) = channel();
    (tx, std::thread::spawn(|| rooster(rx)))
});
fn rooster(rx: Receiver<Sleeper>) {
    let mut heap = BinaryHeap::new();
    while let Some(sleeper) = {
        heap.extend(rx.try_iter());
        heap.pop().or_else(|| rx.recv().ok())
    } {
        match sleeper.until.saturating_duration_since(Instant::now()) {
            Duration::ZERO => sleeper.waker.wake(),
            dur => {
                heap.push(sleeper);
                std::thread::park_timeout(dur);
            }
        }
    }
}

#[cfg(test)]
#[test]
fn sanity_sleeper_heap_order() {
    use futures::executor::block_on;
    block_on(async {
        let waker = waker().await;
        let now = Instant::now();
        let next = now + Duration::from_secs(1);
        let mut heap = BinaryHeap::from_iter([
            Sleeper {
                until: next,
                waker: waker.clone(),
            },
            Sleeper {
                until: now,
                waker: waker.clone(),
            },
        ]);
        assert_eq!(
            heap.pop(),
            Some(Sleeper {
                until: now,
                waker: waker.clone()
            })
        );
        assert_eq!(heap.pop(), Some(Sleeper { until: next, waker }));
        assert_eq!(heap.pop(), None);
    });
}
