use crate::thread_parker::UnparkHandleT;
use std::{task::Poll, time::Instant};

/// Trait for the platform task parker implementation.
///
/// All unsafe methods are unsafe to mirror the `ThreadParkerT` methods.
pub trait TaskParkerT {
    type Context<'a>;
    type UnparkHandle: UnparkHandleT;

    fn new(cx: &mut Self::Context<'_>) -> Self;

    /// Checks whether this is a valid `context` to use with this parker.
    fn is_valid_context(&self, cx: &mut Self::Context<'_>) -> bool;

    /// Prepares the parker. This should be called before adding it to the queue.
    unsafe fn prepare_park(&self, cx: &mut Self::Context<'_>);

    /// Checks if the park timed out. This should be called while holding the
    /// queue lock after `park_until` has returned false.
    unsafe fn timed_out(&self, cx: &mut Self::Context<'_>) -> bool;

    /// Parks the task until it is unparked. This should be called after it has
    /// been added to the queue, after unlocking the queue.
    unsafe fn park(&self, cx: &mut Self::Context<'_>) -> Poll<()>;

    /// Parks the task until it is unparked or the timeout is reached. This
    /// should be called after it has been added to the queue, after unlocking
    /// the queue. Returns true if we were unparked and false if we timed out.
    unsafe fn park_until(&self, cx: &mut Self::Context<'_>, timeout: Instant) -> Poll<bool>;

    /// Locks the parker to prevent the target task from exiting.
    /// This is to mirror `ThreadParkerT::unpark_lock`.
    /// This should be called while holding the queue lock.
    unsafe fn unpark_lock(&self) -> Self::UnparkHandle;
}
mod waker;
pub use waker::TaskParker;
