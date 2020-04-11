pub mod simulation;
pub mod wheels;

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
