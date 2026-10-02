use core::sync::atomic::{AtomicBool, Ordering};
use std::io::ErrorKind;
use std::time::Instant;
use std::{
    io,
    os::fortanix_sgx::{
        thread::current as current_tcs,
        usercalls::{
            self,
            raw::{EV_UNPARK, Tcs, WAIT_INDEFINITE},
        },
    },
    thread,
};

// Helper type for putting a thread to sleep until some other thread wakes it up
pub struct ThreadParker {
    parked: AtomicBool,
    tcs: Tcs,
}

impl super::ThreadParkerT for ThreadParker {
    type UnparkHandle = UnparkHandle;

    const IS_CHEAP_TO_CONSTRUCT: bool = true;

    #[inline]
    fn new() -> ThreadParker {
        ThreadParker {
            parked: AtomicBool::new(false),
            tcs: current_tcs(),
        }
    }

    #[inline]
    unsafe fn prepare_park(&self) {
        self.parked.store(true, Ordering::Relaxed);
    }

    #[inline]
    unsafe fn timed_out(&self) -> bool {
        self.parked.load(Ordering::Relaxed)
    }

    #[inline]
    unsafe fn park(&self) {
        while self.parked.load(Ordering::Acquire) {
            let result = usercalls::wait(EV_UNPARK, WAIT_INDEFINITE);
            debug_assert_eq!(result.expect("wait returned error") & EV_UNPARK, EV_UNPARK);
        }
    }

    #[inline]
    unsafe fn park_until(&self, timeout: Instant) -> bool {
        while self.parked.load(Ordering::Acquire) {
            let remaining = match timeout.checked_duration_since(Instant::now()) {
                Some(remaining) => remaining,
                None => {
                    return false;
                }
            };
            let remaining_nanos =
                u128::min(remaining.as_nanos(), WAIT_INDEFINITE as u128 - 1) as u64;

            if let Err(e) = usercalls::wait(EV_UNPARK, remaining_nanos)
                && (e.kind() == ErrorKind::TimedOut || e.kind() == ErrorKind::WouldBlock)
            {
                return false;
            }
        }
        true
    }

    #[inline]
    unsafe fn unpark_lock(&self) -> UnparkHandle {
        // We don't need to lock anything, just clear the state
        self.parked.store(false, Ordering::Release);
        UnparkHandle(self.tcs)
    }
}

pub struct UnparkHandle(Tcs);

impl super::UnparkHandleT for UnparkHandle {
    #[inline]
    unsafe fn unpark(self) {
        let result = usercalls::send(EV_UNPARK, Some(self.0));
        if cfg!(debug_assertions)
            && let Err(error) = result
            // `InvalidInput` may be returned if the thread we send to has
            // already been unparked and exited.
            && error.kind() != io::ErrorKind::InvalidInput
        {
            panic!("send returned an unexpected error: {error:?}");
        }
    }
}

#[inline]
pub fn thread_yield() {
    thread::yield_now();
}
