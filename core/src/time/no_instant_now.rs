use core::time::Duration;

pub type Instant = Duration;

pub fn checked_duration_since(later: Instant, earlier: Instant) -> Option<Duration> {
    later.checked_sub(earlier)
}

pub fn default_now() -> Instant {
    panic!("Set with `parking_lot::time::set_now_fn`.")
}
