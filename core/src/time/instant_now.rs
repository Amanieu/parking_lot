#[cfg(check_duration_since)]
use std::time::Duration;

/// A measurement of a monotonically non-decreasing clock.
pub type Instant = std::time::Instant;

#[cfg(feature = "checked_duration_since")]
pub fn checked_duration_since(later: Instant, earlier: Instant) -> Option<Duration> {
    later.checked_duration_since(earlier)
}

/// Uses `std::time::Instant::now()`
pub fn default_now() -> Instant {
    Instant::now()
}
