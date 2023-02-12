//! This module provides an implementation for an event timer used to drive a discrete event simulation.
//!
//! Its particular feature is that it can skip quickly through periods where no events are schedulled as it doesn't track real time,
//! but rather provides the rate at which the simulation proceeds.
//!
//! Progress in the simulation is driven by repeatedly calling the [next](SimulationTimer::next) function
//! until it returns [SimulationStep::Finished](SimulationStep::Finished) indicating that the timer is empty
//! and thus the simulation has run to completion.
//!
//! # Example
//! ```
//! # use std::sync::{Arc, Mutex};
//! # use uuid::Uuid;
//! # use std::time::Duration;
//! use hierarchical_hash_wheel_timer::*;
//! use hierarchical_hash_wheel_timer::simulation::*;
//!
//! let mut timer = SimulationTimer::for_uuid_closures();
//!
//! let barrier: Arc<Mutex<bool>> = Arc::new(Mutex::new(false));
//! let barrier2 = barrier.clone();
//! let id = Uuid::new_v4();
//! let delay = Duration::from_millis(150);
//! timer.schedule_action_once(id, delay, move |timer_id|{
//!     println!("Timer function was triggered! Id={:?}", timer_id);
//!     let mut guard = barrier2.lock().unwrap();
//!     *guard = true;
//! });
//! println!("Starting simulation run.");
//! let mut running = true;
//! while running {
//!     match timer.next() {
//!         SimulationStep::Ok => println!("Next!"),
//!         SimulationStep::Finished => running = false,
//!     }
//! }
//! println!("Simulation run done!");
//! let guard = barrier.lock().unwrap();
//! assert_eq!(*guard, true);
//! ```
use super::*;
use crate::wheels::{cancellable::*, *};
use std::{
    fmt::Debug,
    hash::Hash,
    rc::Rc,
    time::{Duration, SystemTime},
};

// Almost the same as `TimerEntry`, but not storing unnecessary things
#[derive(Debug)]
enum SimulationEntry<I, O, P>
where
    I: Hash + Clone + Eq,
    O: OneshotState<Id = I>,
    P: PeriodicState<Id = I>,
{
    OneShot { state: O },
    Periodic { period: Duration, state: P },
}

impl<I, O, P> SimulationEntry<I, O, P>
where
    I: Hash + Clone + Eq + Debug,
    O: OneshotState<Id = I> + Debug,
    P: PeriodicState<Id = I> + Debug,
{
    fn execute(self) -> Option<(Self, Duration)> {
        match self {
            SimulationEntry::OneShot { state } => {
                state.trigger();
                None
            }
            SimulationEntry::Periodic { period, state } => match state.trigger() {
                TimerReturn::Reschedule(new_state) => {
                    let new_entry = SimulationEntry::Periodic {
                        period,
                        state: new_state,
                    };
                    Some((new_entry, period))
                }
                TimerReturn::Cancel => None,
            },
        }
    }

    fn execute_unique_ref(unique_ref: Rc<Self>) -> Option<(Rc<Self>, Duration)> {
        let unique = Rc::try_unwrap(unique_ref).expect("shouldn't hold on to these refs anywhere");
        unique.execute().map(|t| {
            let (new_unique, delay) = t;
            (Rc::new(new_unique), delay)
        })
    }
}

impl<I, O, P> CancellableTimerEntry for SimulationEntry<I, O, P>
where
    I: Hash + Clone + Eq + Debug,
    O: OneshotState<Id = I> + Debug,
    P: PeriodicState<Id = I> + Debug,
{
    type Id = I;

    fn id(&self) -> &Self::Id {
        match self {
            SimulationEntry::OneShot { state, .. } => state.id(),
            SimulationEntry::Periodic { state, .. } => state.id(),
        }
    }
}

/// A timer implementation that used virtual time
///
/// Time is simply advanced until the next event is scheduled.
pub struct SimulationTimer<I, O, P>
where
    I: Hash + Clone + Eq + Debug,
    O: OneshotState<Id = I> + Debug,
    P: PeriodicState<Id = I> + Debug,
{
    time: u128,
    timer: QuadWheelWithOverflow<SimulationEntry<I, O, P>>,
}

impl<I, O, P> SimulationTimer<I, O, P>
where
    I: Hash + Clone + Eq + Debug,
    O: OneshotState<Id = I> + Debug,
    P: PeriodicState<Id = I> + Debug,
{
    /// Create a new simulation timer starting at `0`
    pub fn new() -> Self {
        SimulationTimer {
            time: 0u128,
            timer: QuadWheelWithOverflow::new(),
        }
    }

    /// Create a new simulation timer starting at a system clock value
    pub fn at(now: SystemTime) -> Self {
        let t = now
            .duration_since(SystemTime::UNIX_EPOCH)
            .expect("SystemTime before UNIX EPOCH!");
        let tms = t.as_millis();
        SimulationTimer {
            time: tms,
            timer: QuadWheelWithOverflow::new(),
        }
    }

    /// Return the timers current virtual time value (in ms)
    pub fn current_time(&self) -> u128 {
        self.time
    }

    /// Advance the virtual time
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> SimulationStep {
        loop {
            match self.timer.can_skip() {
                Skip::Empty => return SimulationStep::Finished,
                Skip::None => {
                    let res = self.timer.tick();
                    self.time += 1u128;
                    if !res.is_empty() {
                        for e in res {
                            self.trigger_entry(e);
                        }
                        return SimulationStep::Ok;
                    }
                }
                Skip::Millis(ms) => {
                    self.timer.skip(ms);
                    self.time += ms as u128;
                    let res = self.timer.tick();
                    self.time += 1u128;
                    if !res.is_empty() {
                        for e in res {
                            self.trigger_entry(e);
                        }
                        return SimulationStep::Ok;
                    }
                }
            }
        }
    }

    fn trigger_entry(&mut self, e: Rc<SimulationEntry<I, O, P>>) {
        if let Some((new_e, delay)) = SimulationEntry::execute_unique_ref(e) {
            match self.timer.insert_ref_with_delay(new_e, delay) {
                Ok(_) => (), // ok
                Err(TimerError::Expired(e)) => panic!(
                    "Trying to insert periodic timer entry with 0ms period! {:?}",
                    e
                ),
                Err(f) => panic!("Could not insert timer entry! {:?}", f),
            }
        } // otherwise, timer is not rescheduled
    }
}

impl<I, O, P> Default for SimulationTimer<I, O, P>
where
    I: Hash + Clone + Eq + Debug,
    O: OneshotState<Id = I> + Debug,
    P: PeriodicState<Id = I> + Debug,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<I> SimulationTimer<I, OneShotClosureState<I>, PeriodicClosureState<I>>
where
    I: Hash + Clone + Eq + Debug,
{
    /// Shorthand for creating a simulation timer using closure state
    pub fn for_closures() -> Self {
        Self::new()
    }
}

#[cfg(feature = "uuid-extras")]
impl
    SimulationTimer<uuid::Uuid, OneShotClosureState<uuid::Uuid>, PeriodicClosureState<uuid::Uuid>>
{
    /// Shorthand for creating a simulation timer using Uuid identifiers and closure state
    pub fn for_uuid_closures() -> Self {
        Self::new()
    }
}

/// Result of advancing virtual time
pub enum SimulationStep {
    /// No timer entries remain
    ///
    /// The simulation can be considered complete.
    Finished,
    /// Step was executed, but more timer entries remain
    ///
    /// Continue calling [next](SimulationTimer::next) to advance virtual time.
    Ok,
}

impl<I, O, P> Timer for SimulationTimer<I, O, P>
where
    I: Hash + Clone + Eq + Debug,
    O: OneshotState<Id = I> + Debug,
    P: PeriodicState<Id = I> + Debug,
{
    type Id = I;
    type OneshotState = O;
    type PeriodicState = P;

    fn schedule_once(&mut self, timeout: Duration, state: Self::OneshotState) {
        let e = SimulationEntry::OneShot { state };
        match self.timer.insert_ref_with_delay(Rc::new(e), timeout) {
            Ok(_) => (), // ok
            Err(TimerError::Expired(e)) => {
                if SimulationEntry::execute_unique_ref(e).is_none() {
                    // do nothing
                } else {
                    // clearly a OneShot
                    unreachable!("OneShot produced reschedule!")
                }
            }
            Err(f) => panic!("Could not insert timer entry! {:?}", f),
        }
    }

    fn schedule_periodic(&mut self, delay: Duration, period: Duration, state: Self::PeriodicState) {
        let e = SimulationEntry::Periodic { period, state };
        match self.timer.insert_ref_with_delay(Rc::new(e), delay) {
            Ok(_) => (), // ok
            Err(TimerError::Expired(e)) => {
                if let Some((new_e, delay)) = SimulationEntry::execute_unique_ref(e) {
                    match self.timer.insert_ref_with_delay(new_e, delay) {
                        Ok(_) => (), // ok
                        Err(TimerError::Expired(e)) => panic!(
                            "Trying to insert periodic timer entry with 0ms period! {:?}",
                            e
                        ),
                        Err(f) => panic!("Could not insert timer entry! {:?}", f),
                    }
                }
            } // otherwise, timer decided not to reschedule itself
            Err(f) => panic!("Could not insert timer entry! {:?}", f),
        }
    }

    fn cancel(&mut self, id: &Self::Id) {
        match self.timer.cancel(id) {
            Ok(_) => (),                                                             // great
            Err(f) => eprintln!("Could not cancel timer with id={:?}. {:?}", id, f), // not so great, but meh
        }
    }
}

#[cfg(feature = "uuid-extras")]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_helpers::*;
    use std::sync::{Arc, Mutex};
    use uuid::Uuid;

    #[test]
    fn simple_simulation() {
        let num = 10usize;
        let mut barriers: Vec<Arc<Mutex<bool>>> = Vec::with_capacity(num);
        let mut timer = SimulationTimer::for_uuid_closures();
        for i in 0..num {
            let barrier = Arc::new(Mutex::new(false));
            barriers.push(barrier.clone());
            let id = Uuid::new_v4();
            let timeout = fib_time(i);
            timer.schedule_action_once(id, timeout, move |_| {
                println!("Running action {}", i);
                let mut guard = barrier.lock().unwrap();
                *guard = true;
            });
        }
        let mut running = true;
        while running {
            match timer.next() {
                SimulationStep::Ok => println!("Next!"),
                SimulationStep::Finished => running = false,
            }
        }
        println!("Simulation run done!");
        for b in barriers {
            let guard = b.lock().unwrap();
            assert_eq!(*guard, true);
        }
    }

    #[test]
    fn rescheduling_simulation() {
        let num = 10usize;
        let mut barriers: Vec<Arc<Mutex<bool>>> = Vec::with_capacity(num);
        let mut timer = SimulationTimer::for_uuid_closures();
        for i in 1..num {
            let barrier = Arc::new(Mutex::new(false));
            barriers.push(barrier.clone());
            let id = Uuid::new_v4();
            let timeout = fib_time(i);
            let mut counter: usize = 5;
            timer.schedule_action_periodic(id, timeout, timeout, move |_| {
                println!("Running action {}", i);
                if counter > 0 {
                    counter -= 1;
                    TimerReturn::Reschedule(())
                } else {
                    let mut guard = barrier.lock().unwrap();
                    *guard = true;
                    TimerReturn::Cancel
                }
            });
        }
        let mut running = true;
        while running {
            match timer.next() {
                SimulationStep::Ok => println!("Next!"),
                SimulationStep::Finished => running = false,
            }
        }
        println!("Simulation run done!");
        for b in barriers {
            let guard = b.lock().unwrap();
            assert_eq!(*guard, true);
        }
    }
}
