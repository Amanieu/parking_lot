// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! A simple spin lock based thread parker. Used on platforms without better
//! parking facilities available.

use crate::thread_parker::UnparkHandleT;
use core::sync::atomic::{AtomicBool, Ordering};
use std::task::{Context, Poll, Waker};
use std::time::Instant;

// Helper type for putting a thread to sleep until some other thread wakes it up
pub struct TaskParker {
    parked: AtomicBool,
    waker: Waker,
}

impl super::TaskParkerT for TaskParker {
    type UnparkHandle = UnparkHandle;

    #[inline]
    fn new(cx: &mut Context<'_>) -> TaskParker {
        TaskParker {
            parked: AtomicBool::new(false),
            waker: cx.waker().clone(),
        }
    }

    #[inline]
    unsafe fn prepare_park(&self, cx: &mut Context<'_>) {
        assert!(
            self.waker.will_wake(cx.waker()),
            "Called TaskParker::prepare_park with unrelated context."
        );
        self.parked.store(true, Ordering::Relaxed);
    }

    #[inline]
    unsafe fn timed_out(&self, cx: &mut Context<'_>) -> bool {
        assert!(
            self.waker.will_wake(cx.waker()),
            "Called TaskParker::timed_out with unrelated context."
        );
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
        // TODO: Schedule wake.
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
