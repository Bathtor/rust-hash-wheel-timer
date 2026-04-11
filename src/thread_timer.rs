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
use crate::{
    queue_timer::{ClockRef, QueueTimerControl, QueueTimerCore, TimerMsg},
    wheels::Skip,
};
use channel::select;
use crossbeam_channel as channel;
use std::{cmp::Ordering, fmt, io, thread, time::Instant};

pub use crate::queue_timer::TimerRef;

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
        let (sender, receiver) = channel::unbounded();
        let handle = thread::Builder::new()
            .name("timer-thread".to_string())
            .spawn(move || {
                let timer = TimerThread::new(receiver);
                timer.run();
            })?;
        Ok(TimerWithThread {
            timer_thread: handle,
            work_queue: sender,
        })
    }

    /// Returns a shareable reference to this timer
    ///
    /// The reference contains the timer's work queue
    /// and can be used to schedule timeouts on this timer.
    pub fn timer_ref(&self) -> TimerRef<I, O, P> {
        TimerRef::new(self.work_queue.clone(), ClockRef::realtime())
    }

    /// Shut this timer down
    ///
    /// In particular, this method waits for the timer's thread to be
    /// joined, or returns an error.
    pub fn shutdown(self) -> Result<(), ThreadTimerError<I, O, P>> {
        self.work_queue
            .send(TimerMsg::Stop)
            .unwrap_or_else(|error| eprintln!("Could not send Stop msg: {:?}", error));
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
            .unwrap_or_else(|error| eprintln!("Could not send Stop msg: {:?}", error));
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

struct TimerThread<I, O, P>
where
    I: Hash + Clone + Eq + fmt::Debug,
    O: OneshotState<Id = I> + fmt::Debug,
    P: PeriodicState<Id = I> + fmt::Debug,
{
    core: QueueTimerCore<I, O, P>,
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
    fn new(work_queue: channel::Receiver<TimerMsg<I, O, P>>) -> Self {
        Self {
            core: QueueTimerCore::new(work_queue),
            running: true,
            start: Instant::now(),
            last_check: 0,
        }
    }

    fn run(mut self) {
        while self.running {
            let elapsed = self.elapsed();
            if elapsed > 0 {
                for _ in 0..elapsed {
                    self.core.tick();
                }
            }

            match self.core.try_recv() {
                Ok(message) => self.apply_message(message),
                Err(channel::TryRecvError::Empty) => match self.core.can_skip() {
                    Skip::None => {
                        thread::yield_now(); // Try again after yielding for a bit.
                    }
                    Skip::Empty => {
                        // Wait until something is scheduled.
                        // Don't even need to bother skipping time in the wheel,
                        // since all times in there are relative.
                        match self.core.recv() {
                            Ok(message) => {
                                self.reset(); // Since we waited for an arbitrary time and taking a new timestamp incurs no error.
                                self.apply_message(message);
                            }
                            Err(channel::RecvError) => {
                                panic!("Timer work_queue unexpectedly shut down!")
                            }
                        }
                    }
                    Skip::Millis(can_skip) if can_skip > 5 => {
                        // Wait until something is scheduled but max can_skip.
                        let waiting_time = can_skip - 5; // Balance OS scheduler inaccuracy.
                        let timeout = Duration::from_millis(u64::from(waiting_time));
                        let result = select! {
                            recv(self.core.work_queue()) -> message => message.ok(),
                            default(timeout) => None,
                        };
                        let elapsed = self.elapsed();
                        self.skip_and_tick(can_skip, elapsed);
                        if let Some(message) = result {
                            self.apply_message(message);
                        }
                    }
                    Skip::Millis(can_skip) => {
                        thread::yield_now();
                        let elapsed = self.elapsed();
                        self.skip_and_tick(can_skip, elapsed);
                    }
                },
                Err(channel::TryRecvError::Disconnected) => {
                    panic!("Timer work_queue unexpectedly shut down!")
                }
            }
        }
    }

    #[inline(always)]
    fn skip_and_tick(&mut self, can_skip: u32, elapsed: u128) {
        let can_skip_u128 = u128::from(can_skip);

        match elapsed.cmp(&can_skip_u128) {
            Ordering::Greater => {
                // It took longer to get rescheduled than we wanted.
                self.core.skip(can_skip);
                let ticks = elapsed - can_skip_u128;
                for _ in 0..ticks {
                    self.core.tick();
                }
            }
            Ordering::Less => {
                // We got woken up early, no need to tick.
                self.core.skip(elapsed as u32);
            }
            Ordering::Equal => {
                // elapsed == can_skip
                self.core.skip(can_skip);
            }
        }
    }

    #[inline(always)]
    fn elapsed(&mut self) -> u128 {
        let elapsed = self.start.elapsed().as_millis();
        let relative_elapsed = elapsed - self.last_check;
        self.last_check = elapsed;
        relative_elapsed
    }

    #[inline(always)]
    fn reset(&mut self) {
        self.start = Instant::now();
        self.last_check = 0;
    }

    #[inline(always)]
    fn apply_message(&mut self, message: TimerMsg<I, O, P>) {
        if matches!(self.core.handle_msg(message), QueueTimerControl::Stop) {
            self.running = false;
        }
    }
}

#[cfg(feature = "uuid-extras")]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_helpers::*;
    use crossbeam_channel as channel;
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
                let elapsed = now.elapsed().as_nanos();
                let target = timeout.as_nanos();
                match elapsed.cmp(&target) {
                    Ordering::Greater => {
                        let diff = ((elapsed - target) as f64) / 1000000.0;
                        println!("Running action {} {}ms late", i, diff);
                    }
                    Ordering::Less => {
                        let diff = ((target - elapsed) as f64) / 1000000.0;
                        println!("Running action {} {}ms early", i, diff);
                    }
                    Ordering::Equal => {
                        println!("Running action {} exactly on time", i);
                    }
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
        for barrier in barriers {
            let guard = barrier.lock().unwrap();
            assert!(*guard);
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
        for barrier in barriers {
            let guard = barrier.lock().unwrap();
            assert!(*guard);
        }
    }

    #[test]
    fn timer_ref_now_inside_handler_is_not_earlier_than_due_time() {
        let timer_core = TimerWithThread::for_uuid_closures();
        let mut timer_ref = timer_core.timer_ref();
        let scheduled_from = timer_ref.now();
        let delay = Duration::from_millis(20);
        let deadline = scheduled_from
            .checked_add(delay)
            .expect("thread timer deadline should not overflow");
        let handler_timer_ref = timer_ref.clone();
        let (observed_now_sender, observed_now_receiver) = channel::bounded(1);

        timer_ref.schedule_action_once(Uuid::new_v4(), delay, move |_| {
            let now = handler_timer_ref.now();
            observed_now_sender
                .send(now)
                .expect("oneshot receiver should stay alive");
        });

        let wait_deadline = Instant::now()
            .checked_add(Duration::from_secs(1))
            .expect("thread timer receive deadline should not overflow");
        let observed_now = observed_now_receiver
            .recv_deadline(wait_deadline)
            .expect("oneshot callback should record observed time before the test deadline");

        timer_core
            .shutdown()
            .expect("Timer didn't shutdown properly!");

        assert!(
            observed_now >= deadline,
            "handler observed {observed_now:?}, which is earlier than scheduled lower bound {deadline:?}"
        );
    }

    /// Check that the TimeRef is cloneable, even if its type parameters aren't.
    #[test]
    fn timer_ref_clone() {
        let timer = TimerWithThread::for_uuid_closures();
        let timer_ref: TimerRef<Uuid, OneShotClosureState<Uuid>, PeriodicClosureState<Uuid>> =
            timer.timer_ref();
        // No need to use it. Just checking that it compiles.
        let _cloned_ref = timer_ref.clone();
    }
}
