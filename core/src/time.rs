//! Allows substitution of the `Instant` type with `Duration` when `Instant::now()` is not supported
//! for a given target.

cfg_if::cfg_if! {
  if #[cfg(feature = "no_instant_now")] {
     mod no_instant_now;
     pub use self::no_instant_now::*;
  } else {
     mod instant_now;
     pub use self::instant_now::*;
  }
}

use crate::word_lock::WordLock;

/// A function that can replace `std::time::Instant::now()` by instead returning an `Instant` even
/// if `std::time::Instant::now()` does not work on a target.
pub type NowFn = fn() -> Instant;

/// Pointer to the current `NowFn` used by `now()`
pub fn get_now_fn() -> NowFn {
    unsafe {
        NOW_FN_LOCK.lock();

        let now_fn = NOW_FN;

        NOW_FN_LOCK.unlock();

        now_fn
    }
}

/// Replaces the current `NowFn` used for `now()` with `now_fn`.
pub fn set_now_fn(now_fn: NowFn) {
    unsafe {
        NOW_FN_LOCK.lock();

        NOW_FN = now_fn;

        NOW_FN_LOCK.unlock();
    }
}

/// Generates an `Instant` using `NowFn` set with `set_now_fn_ptr`
pub fn now() -> Instant {
    get_now_fn()()
}

static NOW_FN_LOCK: WordLock = WordLock::INIT;
static mut NOW_FN: NowFn = default_now;
