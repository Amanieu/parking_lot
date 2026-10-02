use crate::raw_mutex::RawMutex;
use lock_api::RawMutexFair;

/// Raw fair mutex type backed by the parking lot.
pub struct RawFairMutex(RawMutex);

unsafe impl lock_api::RawMutex for RawFairMutex {
    const INIT: Self = RawFairMutex(<RawMutex as lock_api::RawMutex>::INIT);

    type GuardMarker = <RawMutex as lock_api::RawMutex>::GuardMarker;

    #[inline]
    fn lock(&self) {
        self.0.lock()
    }

    #[inline]
    fn try_lock(&self) -> bool {
        self.0.try_lock()
    }

    #[inline]
    unsafe fn unlock(&self) {
        unsafe { self.unlock_fair() }
    }

    #[inline]
    fn is_locked(&self) -> bool {
        self.0.is_locked()
    }
}

unsafe impl lock_api::RawMutexFair for RawFairMutex {
    #[inline]
    unsafe fn unlock_fair(&self) {
        unsafe { self.0.unlock_fair() }
    }

    #[inline]
    unsafe fn bump(&self) {
        unsafe { self.0.bump() }
    }
}

unsafe impl lock_api::RawMutexTimed for RawFairMutex {
    type Duration = <RawMutex as lock_api::RawMutexTimed>::Duration;
    type Instant = <RawMutex as lock_api::RawMutexTimed>::Instant;

    #[inline]
    fn try_lock_until(&self, timeout: Self::Instant) -> bool {
        self.0.try_lock_until(timeout)
    }

    #[inline]
    fn try_lock_for(&self, timeout: Self::Duration) -> bool {
        self.0.try_lock_for(timeout)
    }
}
