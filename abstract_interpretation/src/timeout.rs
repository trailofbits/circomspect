//! Cooperative wall-clock limits for one analysis scope.

use std::cell::Cell;
use std::panic::{AssertUnwindSafe, catch_unwind, resume_unwind};
use std::time::{Duration, Instant};

/// Per-scope analysis limit. An unlimited run has no deadline checks to satisfy.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Timeout {
    Unlimited,
    Bounded(Duration),
}

#[derive(Clone, Copy)]
struct Deadline {
    start: Instant,
    limit: Duration,
}

/// A scope exceeded its configured wall-clock limit.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TimeoutExceeded;

thread_local! {
    static DEADLINE: Cell<Option<Deadline>> = const { Cell::new(None) };
}

/// Run one scope with a deadline and discard its result if the deadline expires.
///
/// # Errors
/// Returns `TimeoutExceeded` when a checkpoint observes an expired deadline.
///
/// # Panics
/// A panic other than the timeout marker is resumed unchanged.
pub fn within<T>(timeout: Timeout, work: impl FnOnce() -> T) -> Result<T, TimeoutExceeded> {
    let deadline = match timeout {
        Timeout::Unlimited => None,
        Timeout::Bounded(limit) => Some(Deadline { start: Instant::now(), limit }),
    };
    let previous = DEADLINE.with(|slot| slot.replace(deadline));
    let result = catch_unwind(AssertUnwindSafe(|| {
        check();
        let value = work();
        check();
        value
    }));
    DEADLINE.with(|slot| slot.set(previous));
    match result {
        Ok(value) => Ok(value),
        Err(payload) if payload.is::<TimeoutExceeded>() => Err(TimeoutExceeded),
        Err(payload) => resume_unwind(payload),
    }
}

/// Stop the current scope when its cooperative deadline has expired.
///
/// # Panics
/// Unwinds with a private marker to the nearest `within` boundary on timeout.
pub fn check() {
    let expired = DEADLINE
        .with(|slot| slot.get().is_some_and(|deadline| deadline.start.elapsed() >= deadline.limit));
    if expired {
        resume_unwind(Box::new(TimeoutExceeded));
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use crate::timeout::{Timeout, TimeoutExceeded, check, within};

    #[test]
    fn expired_scope_does_not_run_work_or_affect_the_next_scope() {
        let mut ran = false;
        assert_eq!(within(Timeout::Bounded(Duration::ZERO), || ran = true), Err(TimeoutExceeded));
        assert!(!ran);
        assert_eq!(
            within(Timeout::Unlimited, || {
                check();
                7
            }),
            Ok(7)
        );
    }

    #[test]
    fn elapsed_work_cannot_return_a_completed_result() {
        let result = within(Timeout::Bounded(Duration::from_millis(1)), || {
            std::thread::sleep(Duration::from_millis(10));
        });
        assert_eq!(result, Err(TimeoutExceeded));
    }

    #[test]
    fn ordinary_panics_are_not_reported_as_timeouts() {
        let failure = std::panic::catch_unwind(|| {
            let _ = within(Timeout::Bounded(Duration::from_secs(5)), || panic!("analysis bug"));
        });
        assert!(failure.is_err());
        assert_eq!(within(Timeout::Unlimited, || 7), Ok(7));
    }
}
