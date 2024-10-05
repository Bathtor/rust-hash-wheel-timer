//! This crate provides a low-level event timer implementation
//! based on hierarchical hash wheels.
//!
//! The APIs in the crate are offered at three different levels of abstraction,
//! listed below from lowest to highest.
//!
//! # 1 – Single Wheel
//! The fundamental abstraction of this crate a single hash wheel with 256 slots
//! addressed with a single byte. Each slot stores a list of a generic event type.
//! The whole wheel can be "ticked" causing entries in the slots that are being moved over
//! to expire. With every tick, all expired event entries are returned for handling.
//! For more details see the [byte_wheel](wheels::byte_wheel) module.
//!
//! # 2 – Hierachical Wheel
//! Combining four byte wheels we get a hierachical timer that can represent timeouts
//! up to [`u32::MAX`](std::u32::MAX) time units into the future.
//! In order to support timeouts of up to [`u64::MAX`](std::u64::MAX) time units,
//! our implementations also come with an overflow list, which stores all timers that didn't fit
//! into any slot in the four wheels. Addition into this list happens in (amortised) constant time
//! but movement from the list into the timer array is linear in the number of overflow items.
//! Our design assumed that the vast majority of timers are going be scheduled less than
//! [`u32::MAX`](std::u32::MAX) time units into the future. However, as movement from the overflow list
//! still happens at a rate of over 6mio entries per second (on a 2019 16"MBP) for most applications
//! there should be no large issues even if this assumption is not correct.
//!
//! This crate provides two variant implementations of this four level wheel structure:
//!
//! - The [quad_wheel::QuadWheelWithOverflow](wheels::quad_wheel::QuadWheelWithOverflow) corresponds directly to the implementation described above.
//! - The [cancellable::QuadWheelWithOverflow](wheels::cancellable::QuadWheelWithOverflow) additionally supports the cancellation of outstanding timers
//!   before they expire. In order to do so, however, it requires the generic timer entry type to provide a unique identifier field. It also uses
//!   [Rc](std::rc::Rc) internally to avoid double storing the actual entry, which makes it (potentialy) unsuitable for situations where the timer must
//!   be able to move threads (since Rc](std::rc::Rc) is not `Send`).
//!
//! # 3 – High Level APIs
//! This crate also provides two high levels APIs that can either be used directly or can be seen as examples
//! of how to use the lower level APIs in an application.
//!
//! Bother higher level APIs also offer built-in support for periodically repeating timers, in addition to the normal timers
//! which are schedulled once and discarded once expired.
//!
//! ## Simulation Timer
//! The [simulation](simulation) module provides an implementation for an event timer used to drive a discrete event simulation.
//! Its particular feature is that it can skip quickly through periods where no events are schedulled as it doesn't track real time,
//! but rather provides the rate at which the simulation proceeds.
//!
//! ## Thread Timer
//! The [thread_timer](thread_timer) module provides a timer for real-time event schedulling with millisecond accuracy.
//! It runs on its own dedicated thread and uses a shareable handle called a `TimerRef` for communication with other threads.

#![deny(missing_docs)]

use std::{hash::Hash, time::Duration};

pub mod simulation;
pub mod wheels;
use wheels::{cancellable::CancellableTimerEntry, TimerEntryWithDelay};

mod timers;
pub use self::timers::*;

#[cfg(feature = "thread-timer")]
pub mod thread_timer;

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

/// A simple implementation of a timer entry that only stores its own unique id and the original delay
#[derive(Debug)]
pub struct IdOnlyTimerEntry<I> {
    /// The unique identifier part of the entry
    pub id: I,
    /// The delay that this entry is to be schedulled with (i.e., expire after)
    pub delay: Duration,
}
impl<I> IdOnlyTimerEntry<I> {
    /// Create a new timer entry from the id and the delay after which it should expire
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

/// A module with some convenince functions for writing timer tests
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
