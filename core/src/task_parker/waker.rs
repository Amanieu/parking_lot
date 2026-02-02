// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! A simple spin lock based thread parker. Used on platforms without better
//! parking facilities available.

use core::sync::atomic::{AtomicBool, Ordering};
use std::future::Future;
use std::mem::take;
use std::pin::Pin;
use std::task::{Context, Poll, Waker};
use std::time::Instant;

use crate::thread_parker::UnparkHandleT;

// Helper type for putting a thread to sleep until some other thread wakes it up
pub struct TaskParker {
    parked: AtomicBool,
    waker: Waker,
}

impl super::TaskParkerT for TaskParker {
    type UnparkHandle = UnparkHandle;

    const IS_CHEAP_TO_CONSTRUCT: bool = true;

    #[inline]
    fn new(cx: &mut Context<'_>) -> TaskParker {
        TaskParker {
            parked: AtomicBool::new(false),
            waker: cx.waker().clone(),
        }
    }

    #[inline]
    unsafe fn prepare_park(&self) {
        self.parked.store(true, Ordering::Relaxed);
    }

    #[inline]
    unsafe fn timed_out(&self) -> bool {
        self.parked.load(Ordering::Relaxed) != false
    }

    #[inline]
    unsafe fn park(&self, cx: &mut Context<'_>) -> Poll<()> {
        assert!(
            self.waker.will_wake(cx.waker()),
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
        match self.park(cx) {
            Poll::Ready(()) => Poll::Ready(true),
            Poll::Pending if Instant::now() >= timeout => Poll::Ready(false),
            Poll::Pending => Poll::Pending,
        }
    }

    #[inline]
    unsafe fn unpark_lock(&self) -> UnparkHandle {
        // We don't need to lock anything, just clear the state
        self.parked.store(false, Ordering::Release);
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

#[derive(Debug)]
pub struct Yield {
    once: bool,
}
impl Future for Yield {
    type Output = ();
    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        if take(&mut self.once) {
            Poll::Pending
        } else {
            Poll::Ready(())
        }
    }
}

#[inline]
pub async fn task_yield() -> Yield {
    Yield { once: true }
}
