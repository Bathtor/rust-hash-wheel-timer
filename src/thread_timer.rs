//! This module provides a timer for real-time event schedulling with millisecond accuracy.
//!
//! It runs on its own dedicated thread and uses a shareable handle called a `TimerRef` for communication with other threads.
//! This inter-thread communication is based on [crossbeam_channel](crossbeam_channel).
//!
//! ## Note
//! Sine this timer runs on its own thread, instance creation will fail if the generic id or state types used are not `Send`.
//!
//! # Example
//! ```
//! # use std::sync::{Arc, Mutex};
//! # use uuid::Uuid;
//! # use std::time::Duration;
//! use hierarchical_hash_wheel_timer::*;
//! use hierarchical_hash_wheel_timer::thread_timer::*;
//!
//! let timer_core = TimerWithThread::for_uuid_closures();
//!
//! let mut timer = timer_core.timer_ref();
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
//! println!("Waiting timing run to finish...");
//! std::thread::sleep(delay);
//! let mut done = false;
//! while !done {
//!     let guard = barrier.lock().unwrap();
//!     done = *guard;
//! }
//! println!("Timing run completed!");
//! drop(timer);
//! timer_core
//!    .shutdown()
//!    .expect("Timer didn't shutdown properly!");
//! ```

use super::*;

use crate::wheels::{cancellable::*, *};
use channel::select;
use crossbeam_channel as channel;
use std::{fmt, io, rc::Rc, thread, time::Instant};

#[derive(Debug)]
enum TimerMsg<I, O, P>
where
    I: Hash + Clone + Eq,
    O: OneshotState<Id = I>,
    P: PeriodicState<Id = I>,
{
    Schedule(TimerEntry<I, O, P>),
    Cancel(I),
    Stop,
}

/// A reference to a thread timer
///
/// This is used to schedule events on the timer from other threads.
///
/// You can get an instance via [timer_ref](TimerWithThread::timer_ref).
#[derive(Clone)]
pub struct TimerRef<I, O, P>
where
    I: Hash + Clone + Eq,
    O: OneshotState<Id = I>,
    P: PeriodicState<Id = I>,
{
    work_queue: channel::Sender<TimerMsg<I, O, P>>,
}

impl<I, O, P> Timer for TimerRef<I, O, P>
where
    I: Hash + Clone + Eq,
    O: OneshotState<Id = I>,
    P: PeriodicState<Id = I>,
{
    type Id = I;
    type OneshotState = O;
    type PeriodicState = P;

    fn schedule_once(&mut self, timeout: Duration, state: Self::OneshotState) -> () {
        let e = TimerEntry::OneShot { timeout, state };
        self.work_queue
            .send(TimerMsg::Schedule(e))
            .unwrap_or_else(|e| eprintln!("Could not send Schedule msg: {:?}", e));
    }

    fn schedule_periodic(
        &mut self,
        delay: Duration,
        period: Duration,
        state: Self::PeriodicState,
    ) -> () {
        let e = TimerEntry::Periodic {
            delay,
            period,
            state,
        };
        self.work_queue
            .send(TimerMsg::Schedule(e))
            .unwrap_or_else(|e| eprintln!("Could not send Schedule msg: {:?}", e));
    }

    fn cancel(&mut self, id: &Self::Id) -> () {
        self.work_queue
            .send(TimerMsg::Cancel(id.clone()))
            .unwrap_or_else(|e| eprintln!("Could not send Cancel msg: {:?}", e));
    }
}

/// A timer implementation that uses its own thread
///
/// This struct acts as a main handle for the timer and its thread.
pub struct TimerWithThread<I, O, P>
where
    I: Hash + Clone + Eq,
    O: OneshotState<Id = I>,
    P: PeriodicState<Id = I>,
{
    timer_thread: thread::JoinHandle<()>,
    work_queue: channel::Sender<TimerMsg<I, O, P>>,
}

impl<I, O, P> TimerWithThread<I, O, P>
where
    I: Hash + Clone + Eq + fmt::Debug + Send + 'static,
    O: OneshotState<Id = I> + fmt::Debug + Send + 'static,
    P: PeriodicState<Id = I> + fmt::Debug + Send + 'static,
{
    /// Create a new timer with its own thread.
    ///
    /// The thread will be called `"timer-thread"`.
    pub fn new() -> io::Result<TimerWithThread<I, O, P>> {
        let (s, r) = channel::unbounded();
        let handle = thread::Builder::new()
            .name("timer-thread".to_string())
            .spawn(move || {
                let timer = TimerThread::new(r);
                timer.run();
            })?;
        let twt = TimerWithThread {
            timer_thread: handle,
            work_queue: s,
        };
        Ok(twt)
    }

    /// Returns a shareable reference to this timer
    ///
    /// The reference contains the timer's work queue
    /// and can be used to schedule timeouts on this timer.
    pub fn timer_ref(&self) -> TimerRef<I, O, P> {
        TimerRef {
            work_queue: self.work_queue.clone(),
        }
    }

    /// Shut this timer down
    ///
    /// In particular, this method waits for the timer's thread to be
    /// joined, or returns an error.
    pub fn shutdown(self) -> Result<(), ThreadTimerError<I, O, P>> {
        self.work_queue
            .send(TimerMsg::Stop)
            .unwrap_or_else(|e| eprintln!("Could not send Stop msg: {:?}", e));
        match self.timer_thread.join() {
            Ok(_) => Ok(()),
            Err(_) => {
                eprintln!("Timer thread panicked!");
                Err(ThreadTimerError::CouldNotJoinThread)
            }
        }
    }

    /// Same as [shutdown](TimerWithThread::shutdown), but doesn't wait for the thread to join
    pub fn shutdown_async(&self) -> Result<(), ThreadTimerError<I, O, P>> {
        self.work_queue
            .send(TimerMsg::Stop)
            .unwrap_or_else(|e| eprintln!("Could not send Stop msg: {:?}", e));
        Ok(())
    }
}

impl<I, O, P> fmt::Debug for TimerWithThread<I, O, P>
where
    I: Hash + Clone + Eq,
    O: OneshotState<Id = I>,
    P: PeriodicState<Id = I>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<TimerWithThread>")
    }
}

#[cfg(feature = "uuid-extras")]
impl
    TimerWithThread<uuid::Uuid, OneShotClosureState<uuid::Uuid>, PeriodicClosureState<uuid::Uuid>>
{
    /// Shorthand for creating a timer instance using Uuid identifiers and closure state
    pub fn for_uuid_closures() -> Self {
        Self::new().expect("timer")
    }
}

/// Errors that can occur when stopping the timer thread
#[derive(Debug)]
pub enum ThreadTimerError<I, O, P>
where
    I: Hash + Clone + Eq,
    O: OneshotState<Id = I>,
    P: PeriodicState<Id = I>,
{
    /// Sending of the `Stop` message failed
    CouldNotSendStopAsync,
    /// Sending of the `Stop` message failed in the waiting case
    ///
    /// This variant returns the original timer instance.
    CouldNotSendStop(TimerWithThread<I, O, P>),
    /// Joining of the timer thread failed
    CouldNotJoinThread,
}

// Almost the same as `TimerEntry`, but not storing unnecessary things
#[derive(Debug)]
enum ThreadTimerEntry<I, O, P>
where
    I: Hash + Clone + Eq,
    O: OneshotState<Id = I>,
    P: PeriodicState<Id = I>,
{
    OneShot { state: O },
    Periodic { period: Duration, state: P },
}

impl<I, O, P> ThreadTimerEntry<I, O, P>
where
    I: Hash + Clone + Eq + fmt::Debug,
    O: OneshotState<Id = I> + fmt::Debug,
    P: PeriodicState<Id = I> + fmt::Debug,
{
    fn from(e: TimerEntry<I, O, P>) -> (Self, Duration) {
        match e {
            TimerEntry::OneShot { timeout, state } => {
                let tte = ThreadTimerEntry::OneShot { state };
                (tte, timeout)
            }
            TimerEntry::Periodic {
                delay,
                period,
                state,
            } => {
                let tte = ThreadTimerEntry::Periodic { period, state };
                (tte, delay)
            }
        }
    }

    fn execute(self) -> Option<(Self, Duration)> {
        match self {
            ThreadTimerEntry::OneShot { state } => {
                state.trigger();
                None
            }
            ThreadTimerEntry::Periodic { period, state } => match state.trigger() {
                TimerReturn::Reschedule(new_state) => {
                    let new_entry = ThreadTimerEntry::Periodic {
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

impl<I, O, P> CancellableTimerEntry for ThreadTimerEntry<I, O, P>
where
    I: Hash + Clone + Eq + fmt::Debug,
    O: OneshotState<Id = I> + fmt::Debug,
    P: PeriodicState<Id = I> + fmt::Debug,
{
    type Id = I;

    fn id(&self) -> &Self::Id {
        match self {
            ThreadTimerEntry::OneShot { state, .. } => state.id(),
            ThreadTimerEntry::Periodic { state, .. } => state.id(),
        }
    }
}

struct TimerThread<I, O, P>
where
    I: Hash + Clone + Eq + fmt::Debug,
    O: OneshotState<Id = I> + fmt::Debug,
    P: PeriodicState<Id = I> + fmt::Debug,
{
    timer: QuadWheelWithOverflow<ThreadTimerEntry<I, O, P>>,
    work_queue: channel::Receiver<TimerMsg<I, O, P>>,
    running: bool,
    start: Instant,
    last_check: u128,
}

impl<I, O, P> TimerThread<I, O, P>
where
    I: Hash + Clone + Eq + fmt::Debug,
    O: OneshotState<Id = I> + fmt::Debug,
    P: PeriodicState<Id = I> + fmt::Debug,
{
    fn new(work_queue: channel::Receiver<TimerMsg<I, O, P>>) -> TimerThread<I, O, P> {
        TimerThread {
            timer: QuadWheelWithOverflow::new(),
            work_queue,
            running: true,
            start: Instant::now(),
            last_check: 0u128,
        }
    }

    fn run(mut self) {
        while self.running {
            let elap = self.elapsed();
            if elap > 0 {
                for _ in 0..elap {
                    self.tick();
                }
            }

            match self.work_queue.try_recv() {
                Ok(msg) => self.handle_msg(msg),
                Err(channel::TryRecvError::Empty) => {
                    match self.timer.can_skip() {
                        Skip::None => {
                            thread::yield_now(); // try again after yielding for a bit
                        }
                        Skip::Empty => {
                            // wait until something is scheduled
                            // don't even need to bother skipping time in the wheel,
                            // since all times in there are relative
                            match self.work_queue.recv() {
                                Ok(msg) => {
                                    self.reset(); // since we waited for an arbitrary time and taking a new timestamp incurs no error
                                    self.handle_msg(msg)
                                }
                                Err(channel::RecvError) => {
                                    panic!("Timer work_queue unexpectedly shut down!")
                                }
                            }
                        }
                        Skip::Millis(can_skip) if can_skip > 5 => {
                            let waiting_time = can_skip - 5; // balance OS scheduler inaccuracy
                                                             // wait until something is scheduled but max skip
                            let timeout = Duration::from_millis(waiting_time as u64);
                            let res = select! {
                                recv(self.work_queue) -> msg => msg.ok(),
                                default(timeout) => None,
                            };
                            let elap = self.elapsed();
                            self.skip_and_tick(can_skip, elap);
                            match res {
                                Some(msg) => self.handle_msg(msg),
                                None => (), // restart loop
                            }
                        }
                        Skip::Millis(can_skip) => {
                            thread::yield_now();
                            let elap = self.elapsed();
                            self.skip_and_tick(can_skip, elap);
                        }
                    }
                }
                Err(channel::TryRecvError::Disconnected) => {
                    panic!("Timer work_queue unexpectedly shut down!")
                }
            }
        }
    }

    #[inline(always)]
    fn skip_and_tick(&mut self, can_skip: u32, elapsed: u128) -> () {
        let can_skip_u128 = can_skip as u128;
        if elapsed > can_skip_u128 {
            // took longer to get rescheduled than we wanted
            self.timer.skip(can_skip);
            let ticks = elapsed - can_skip_u128;
            for _ in 0..ticks {
                self.tick();
            }
        } else if elapsed < can_skip_u128 {
            // we got woken up early, no need to tick
            self.timer.skip(elapsed as u32);
        } else {
            // elapsed == can_skip
            self.timer.skip(can_skip);
        }
    }

    #[inline(always)]
    fn elapsed(&mut self) -> u128 {
        let elap = self.start.elapsed().as_millis();
        let rel_elap = elap - self.last_check;
        self.last_check = elap;
        rel_elap
    }

    #[inline(always)]
    fn reset(&mut self) {
        self.start = Instant::now();
        self.last_check = 0;
    }

    #[inline(always)]
    fn handle_msg(&mut self, msg: TimerMsg<I, O, P>) -> () {
        match msg {
            TimerMsg::Stop => self.running = false,
            TimerMsg::Schedule(entry) => {
                let (e, delay) = ThreadTimerEntry::from(entry);
                match self.timer.insert_ref_with_delay(Rc::new(e), delay) {
                    Ok(_) => (), // ok
                    Err(TimerError::Expired(e)) => {
                        self.trigger_entry(e);
                    }
                    Err(f) => panic!("Could not insert timer entry! {:?}", f),
                }
            }
            TimerMsg::Cancel(ref id) => match self.timer.cancel(id) {
                Ok(_) => (),                     // ok
                Err(TimerError::NotFound) => (), // also ok, might have been triggered already
                Err(f) => panic!("Unexpected error cancelling timer! {:?}", f),
            },
        }
    }

    fn trigger_entry(&mut self, e: Rc<ThreadTimerEntry<I, O, P>>) -> () {
        match ThreadTimerEntry::execute_unique_ref(e) {
            Some((new_e, delay)) => match self.timer.insert_ref_with_delay(new_e, delay) {
                Ok(_) => (), // ok
                Err(TimerError::Expired(e)) => panic!(
                    "Trying to insert periodic timer entry with 0ms period! {:?}",
                    e
                ),
                Err(f) => panic!("Could not insert timer entry! {:?}", f),
            },
            None => (), // ok, timer is not rescheduled
        }
    }

    #[inline(always)]
    fn tick(&mut self) -> () {
        let res = self.timer.tick();
        for e in res {
            self.trigger_entry(e);
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
    fn simple_thread_timing() {
        let num = 20usize;
        let mut barriers: Vec<Arc<Mutex<bool>>> = Vec::with_capacity(num);
        let timer_core = TimerWithThread::for_uuid_closures();
        let mut timer = timer_core.timer_ref();
        let mut total_wait = Duration::from_millis(0);
        println!("Starting timing run.");
        for i in 0..num {
            let barrier = Arc::new(Mutex::new(false));
            barriers.push(barrier.clone());
            let id = Uuid::new_v4();
            let timeout = fib_time(i);
            total_wait += timeout;
            let now = Instant::now();
            timer.schedule_action_once(id, timeout, move |_| {
                let elap = now.elapsed().as_nanos();
                let target = timeout.as_nanos();
                if elap > target {
                    let diff = ((elap - target) as f64) / 1000000.0;
                    println!("Running action {} {}ms late", i, diff);
                } else if elap < target {
                    let diff = ((target - elap) as f64) / 1000000.0;
                    println!("Running action {} {}ms early", i, diff);
                } else {
                    println!("Running action {} exactly on time", i);
                }
                let mut guard = barrier.lock().unwrap();
                *guard = true;
            });
        }
        println!("Waiting timing run to finish {}ms", total_wait.as_millis());
        thread::sleep(total_wait);
        timer_core
            .shutdown()
            .expect("Timer didn't shutdown properly!");
        println!("Timing run done!");
        for b in barriers {
            let guard = b.lock().unwrap();
            assert_eq!(*guard, true);
        }
    }

    #[test]
    fn rescheduling_thread_timing() {
        let num = 15usize;
        let mut barriers: Vec<Arc<Mutex<bool>>> = Vec::with_capacity(num);
        let timer_core = TimerWithThread::for_uuid_closures();
        let mut timer = timer_core.timer_ref();
        let mut total_wait = Duration::from_millis(0);
        println!("Starting timing run.");
        for i in 1..num {
            let barrier = Arc::new(Mutex::new(false));
            barriers.push(barrier.clone());
            let id = Uuid::new_v4();
            let mut counter: u32 = 3;
            let timeout = fib_time(i);
            total_wait += timeout * counter;
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
        println!("Waiting timing run to finish {}ms", total_wait.as_millis());
        thread::sleep(total_wait);
        timer_core
            .shutdown()
            .expect("Timer didn't shutdown properly!");
        println!("Timing run done!");
        for b in barriers {
            let guard = b.lock().unwrap();
            assert_eq!(*guard, true);
        }
    }
}
