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

/// `core::macros::unreachable` in debug mode,
/// `core::hint::unreachable_unchecked()` in release mode
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
    use crate::util::unreachable;
    use std::{
        future::{Future, Ready},
        pin::{pin, Pin},
        task::{Context, Poll, Waker},
    };
    /// An immediate future is one that only needs to access the [Context]
    /// to immediately finish without ever yielding [Poll::Pending]
    /// and therefore can directly return its output without needing to wrap
    /// it in [Poll::Ready].
    ///
    /// Usefull as a kind of halfway-point/intermediary between sync and async execution,
    /// where you do need an asynchronous environment, but don't actually need or want
    /// to be asynchronous yourself.
    pub trait ImmediateFuture: Future {
        /// Consumes this [Future] to immediately return
        /// its output without having to wrap it in [Poll].
        fn poll_ready(self, cx: &mut Context<'_>) -> Self::Output;
    }
    impl<T> ImmediateFuture for Ready<T> {
        fn poll_ready(self, _: &mut Context<'_>) -> Self::Output {
            self.into_inner()
        }
    }
    /// A future that immediately finishes without ever yielding [Poll::Pending].
    ///
    /// Created by [immediate]. See its and [ImmediateFuture]s documentation for more information.
    pub struct Immediate<F = fn(&mut Context<'_>)>(Option<F>);
    impl<F> Unpin for Immediate<F> {}
    impl<F> From<F> for Immediate<F> {
        fn from(value: F) -> Self {
            Self(Some(value))
        }
    }
    impl<T, F: FnOnce(&mut Context<'_>) -> T> Future for Immediate<F> {
        type Output = T;
        fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
            Poll::Ready(self.0.take().expect("polled twice")(cx))
        }
    }
    impl<T, F: FnOnce(&mut Context<'_>) -> T> ImmediateFuture for Immediate<F> {
        fn poll_ready(self, cx: &mut Context<'_>) -> Self::Output {
            self.0.expect("polled twice")(cx)
        }
    }
    impl<T, F> Future for Immediate<(F, fn(F, &mut Context<'_>) -> T)> {
        type Output = T;
        fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
            let (f, ready) = self.0.take().expect("polled twice");
            Poll::Ready(ready(f, cx))
        }
    }
    impl<T, F> ImmediateFuture for Immediate<(F, fn(F, &mut Context<'_>) -> T)> {
        fn poll_ready(mut self, cx: &mut Context<'_>) -> Self::Output {
            let (f, ready) = self.0.take().expect("polled twice");
            ready(f, cx)
        }
    }
    /// Creates a new [ImmediateFuture] wrapping around a function
    /// taking a mutable [Context] reference as its argument and yielding
    /// the return value as its [Future::Output].
    ///
    /// Usefull as a kind of halfway-point/intermediary between sync and async execution,
    /// where you do need an asynchronous environment, but don't actually need or want
    /// to be asynchronous yourself.
    pub fn immediate<T, F: FnOnce(&mut Context<'_>) -> T>(f: F) -> Immediate<F> {
        Immediate::from(f)
    }
    /// Creates a new [ImmediateFuture] wrapping around a value and function
    /// taking that value as well as a mutable [Context] reference as its arguments
    /// and yielding the return value as its [Future::Output].
    ///
    /// Usefull as a kind of halfway-point/intermediary between sync and async execution,
    /// where you do need an asynchronous environment, but don't actually need or want
    /// to be asynchronous yourself.
    pub fn immediate_with<T, F: FnOnce(T, &mut Context<'_>) -> U, U>(
        t: T,
        f: F,
    ) -> Immediate<(T, F)> {
        Immediate::from((t, f))
    }
    /// Creates an [Immediate] wrapping around a future by assuming
    /// that polling it will immediately yield [Poll::Ready],
    /// and panicking if it doesn't.
    ///
    /// # Panics
    ///
    /// Panics on `poll(_ready)` if the underlying future fails to yield [Poll::Ready].
    pub fn assume_immediate<F: Future>(
        f: F,
    ) -> Immediate<(F, fn(F, &mut Context<'_>) -> F::Output)> {
        let ready: fn(F, &mut Context<'_>) -> F::Output = |f, cx| match pin!(f).poll(cx) {
            Poll::Ready(v) => v,
            Poll::Pending => panic!("The future passed to as_immediate yielded Poll::Pending."),
        };
        Immediate::from((f, ready))
    }
    /// Creates an [Immediate] wrapping around a future by assuming
    /// that polling it will immediately yield [Poll::Ready].
    ///
    /// # Safety
    ///
    /// The underlying future must immediately yield [Poll::Ready].
    pub unsafe fn assume_immediate_unchecked<F: Future>(
        f: F,
    ) -> Immediate<(F, fn(F, &mut Context<'_>) -> F::Output)> {
        let ready: fn(F, &mut Context<'_>) -> F::Output = |f, cx| match pin!(f).poll(cx) {
            Poll::Ready(v) => v,
            Poll::Pending => unreachable(),
        };
        Immediate::from((f, ready))
    }
    /// Returns an [ImmediateFuture] that returns the [Waker]
    /// for the current asynchronous [Context].
    pub fn waker() -> Immediate<fn(&mut Context<'_>) -> Waker> {
        immediate(|cx| cx.waker().clone())
    }
}
#[cfg(feature = "async")]
pub use immediate::*;
