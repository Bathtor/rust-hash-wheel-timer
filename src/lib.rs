use std::{hash::Hash, time::Duration};

pub mod simulation;
pub mod wheels;

use wheels::{CancellableTimerEntry, TimerEntryWithDelay};

mod timers;
pub use self::timers::*;

#[cfg(feature = "uuid-extras")]
mod uuid_extras;
#[cfg(feature = "uuid-extras")]
pub use self::uuid_extras::*;

/// Errors encounted by a timer implementation
#[derive(Debug)]
pub enum TimerError<EntryType> {
    /// The timeout with the given id was not found
    NotFound,
    /// The timout has already expired
    Expired(EntryType),
}

#[derive(Debug)]
pub struct IdOnlyTimerEntry<I> {
    pub id: I,
    pub delay: Duration,
}
impl<I> IdOnlyTimerEntry<I> {
    pub fn new(id: I, delay: Duration) -> Self {
        IdOnlyTimerEntry { id, delay }
    }
}
impl<I> CancellableTimerEntry for IdOnlyTimerEntry<I>
where
    I: Hash + Clone + Eq + std::fmt::Debug,
{
    type Id = I;

    fn id(&self) -> &Self::Id {
        &self.id
    }
}

impl<I> TimerEntryWithDelay for IdOnlyTimerEntry<I>
where
    I: Hash + Clone + Eq + std::fmt::Debug,
{
    fn delay(&self) -> Duration {
        self.delay
    }
}

#[cfg(test)]
pub mod test_helpers {
    use std::time::Duration;

    /// Produce a duration corresponding to the i:th Fibonacci number
    ///
    /// Good for testing timer implementations at large a variety of timeout delays.
    pub fn fib_time(mut i: usize) -> Duration {
        if i == 0 {
            Duration::from_millis(0)
        } else if i == 1 {
            Duration::from_millis(1)
        } else {
            let mut fminus2: u64 = 0u64;
            let mut fminus1: u64 = 1u64;
            while i >= 2 {
                let fi = fminus2 + fminus1;
                i -= 1;
                fminus2 = fminus1;
                fminus1 = fi;
            }
            Duration::from_millis(fminus1)
        }
    }
}
