use std::time::{Duration, Instant};

#[inline]
pub fn to_deadline(timeout: Duration) -> Option<Instant> {
    Instant::now().checked_add(timeout)
}
