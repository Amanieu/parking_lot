// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

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

// hint::unreachable_unchecked() in release mode
#[inline]
pub unsafe fn unreachable() -> ! {
    if cfg!(debug_assertions) {
        unreachable!();
    } else {
        core::hint::unreachable_unchecked()
    }
}

#[cfg(feature = "async")]
mod immediate {
    use std::{
        future::{Future, Ready},
        pin::Pin,
        task::{Context, Poll, Waker},
    };
    pub trait ImmediateFuture: Future {
        fn poll_ready(self, cx: &mut Context<'_>) -> Self::Output;
    }
    impl<T> ImmediateFuture for Ready<T> {
        fn poll_ready(self, _: &mut Context<'_>) -> Self::Output {
            self.into_inner()
        }
    }
    pub struct Immediate<F = fn(&mut Context<'_>)>(Option<F>);
    impl<F> From<F> for Immediate<F> {
        fn from(value: F) -> Self {
            Self(Some(value))
        }
    }
    impl<T, F: Unpin + FnOnce(&mut Context<'_>) -> T> Future for Immediate<F> {
        type Output = T;
        fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
            Poll::Ready(self.0.take().expect("polled twice")(cx))
        }
    }
    impl<T, F: Unpin + FnOnce(&mut Context<'_>) -> T> ImmediateFuture for Immediate<F> {
        fn poll_ready(self, cx: &mut Context<'_>) -> Self::Output {
            self.0.expect("polled twice")(cx)
        }
    }
    pub fn immediate<T, F: FnOnce(&mut Context<'_>) -> T>(f: F) -> Immediate<F> {
        Immediate::from(f)
    }
    pub fn current_waker() -> Immediate<fn(&mut Context<'_>) -> Waker> {
        immediate(|cx| cx.waker().clone())
    }
}
#[cfg(feature = "async")]
pub use immediate::*;
