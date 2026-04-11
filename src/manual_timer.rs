//! This module provides a manually-driven timer with the same queue-based
//! scheduling handle as the threaded timer.
//!
//! The timer does not own a worker thread. Instead, tests or simulations drive
//! time forward explicitly through [`ManualTimer::advance_by`] or
//! [`ManualTimer::advance_to_next`].

use super::*;
use crate::{
    queue_timer::{ClockRef, QueueTimerControl, QueueTimerCore, TimerMsg, TimerRef},
    wheels::Skip,
};
use crossbeam_channel as channel;
use std::{
    fmt,
    hash::Hash,
    sync::{
        atomic::{AtomicU64, Ordering},
        Arc,
        Mutex,
    },
    time::{Duration, Instant},
};

/// A timer implementation advanced explicitly by the caller.
///
/// This timer is useful for tests that need deterministic control over timeout
/// delivery without depending on wall-clock time or an extra scheduling thread.
pub struct ManualTimer<I, O, P>
where
    I: Hash + Clone + Eq + fmt::Debug,
    O: OneshotState<Id = I> + fmt::Debug,
    P: PeriodicState<Id = I> + fmt::Debug,
{
    inner: Arc<Mutex<ManualTimerInner<I, O, P>>>,
    work_queue: channel::Sender<TimerMsg<I, O, P>>,
    base: Instant,
    elapsed_millis: Arc<AtomicU64>,
}

impl<I, O, P> ManualTimer<I, O, P>
where
    I: Hash + Clone + Eq + fmt::Debug,
    O: OneshotState<Id = I> + fmt::Debug,
    P: PeriodicState<Id = I> + fmt::Debug,
{
    /// Create a new manual timer.
    pub fn new() -> Self {
        let (work_queue, receiver) = channel::unbounded();
        let elapsed_millis = Arc::new(AtomicU64::new(0));
        let inner = ManualTimerInner::new(receiver, Arc::clone(&elapsed_millis));
        Self {
            inner: Arc::new(Mutex::new(inner)),
            work_queue,
            base: Instant::now(),
            elapsed_millis,
        }
    }

    /// Returns a shareable scheduling handle for this timer.
    pub fn timer_ref(&self) -> TimerRef<I, O, P> {
        TimerRef::new(
            self.work_queue.clone(),
            ClockRef::manual(self.base, Arc::clone(&self.elapsed_millis)),
        )
    }

    /// Advances the timer by the supplied duration.
    ///
    /// The timer has millisecond resolution, matching the threaded timer.
    /// Sub-millisecond advances are accumulated and take effect once they sum
    /// to at least one millisecond.
    pub fn advance_by(&self, duration: Duration) {
        let mut inner = self.inner.lock().expect("manual timer mutex poisoned");
        inner.advance_by(duration);
    }

    /// Advances the timer just far enough to trigger the next due timeout.
    ///
    /// Returns `false` when there is currently no outstanding timeout to fire.
    pub fn advance_to_next(&self) -> bool {
        let mut inner = self.inner.lock().expect("manual timer mutex poisoned");
        inner.advance_to_next()
    }

    /// Returns the elapsed logical time since this manual timer was created.
    ///
    /// This is rounded down to the manual timer's millisecond resolution so it
    /// agrees with the deadlines the wheel can actually execute.
    pub fn elapsed(&self) -> Duration {
        Duration::from_millis(self.elapsed_millis.load(Ordering::Acquire))
    }

    /// Returns whether the timer has neither queued commands nor scheduled
    /// deadlines left to execute.
    pub fn is_idle(&self) -> bool {
        let mut inner = self.inner.lock().expect("manual timer mutex poisoned");
        inner.prepare();
        !inner.running || inner.core.is_idle()
    }

    /// Stops this shared manual timer so future advances no longer execute
    /// queued work, even through other clones of the same timer handle.
    pub fn stop(&self) {
        let mut inner = self.inner.lock().expect("manual timer mutex poisoned");
        inner.running = false;
    }
}

impl<I, O, P> Clone for ManualTimer<I, O, P>
where
    I: Hash + Clone + Eq + fmt::Debug,
    O: OneshotState<Id = I> + fmt::Debug,
    P: PeriodicState<Id = I> + fmt::Debug,
{
    fn clone(&self) -> Self {
        Self {
            inner: Arc::clone(&self.inner),
            work_queue: self.work_queue.clone(),
            base: self.base,
            elapsed_millis: Arc::clone(&self.elapsed_millis),
        }
    }
}

impl<I, O, P> Default for ManualTimer<I, O, P>
where
    I: Hash + Clone + Eq + fmt::Debug,
    O: OneshotState<Id = I> + fmt::Debug,
    P: PeriodicState<Id = I> + fmt::Debug,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<I, O, P> fmt::Debug for ManualTimer<I, O, P>
where
    I: Hash + Clone + Eq + fmt::Debug,
    O: OneshotState<Id = I> + fmt::Debug,
    P: PeriodicState<Id = I> + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<ManualTimer>")
    }
}

struct ManualTimerInner<I, O, P>
where
    I: Hash + Clone + Eq + fmt::Debug,
    O: OneshotState<Id = I> + fmt::Debug,
    P: PeriodicState<Id = I> + fmt::Debug,
{
    core: QueueTimerCore<I, O, P>,
    /// Shared logical clock visible to non-blocking readers through `TimerRef::now()`.
    elapsed_millis: Arc<AtomicU64>,
    /// Carries sub-millisecond advances until they add up to one wheel tick.
    sub_millis_remainder: Duration,
    /// Counts how many logical milliseconds have already been applied to the wheel.
    processed_millis: u64,
    running: bool,
}

// Safety: the queue timer core still uses `Rc`/`Weak` internally through the
// cancellable wheel implementation, but a `ManualTimerInner` is only ever
// accessed while holding the surrounding `Mutex`. The shared scheduling handle
// talks to the timer over a channel and never touches the wheel state
// directly, so moving the manually-driven timer between threads is sound as
// long as the user-provided timer state is itself `Send`.
unsafe impl<I, O, P> Send for ManualTimerInner<I, O, P>
where
    I: Hash + Clone + Eq + fmt::Debug + Send,
    O: OneshotState<Id = I> + fmt::Debug + Send,
    P: PeriodicState<Id = I> + fmt::Debug + Send,
{
}

impl<I, O, P> ManualTimerInner<I, O, P>
where
    I: Hash + Clone + Eq + fmt::Debug,
    O: OneshotState<Id = I> + fmt::Debug,
    P: PeriodicState<Id = I> + fmt::Debug,
{
    fn new(
        work_queue: channel::Receiver<TimerMsg<I, O, P>>,
        elapsed_millis: Arc<AtomicU64>,
    ) -> Self {
        Self {
            core: QueueTimerCore::new(work_queue),
            elapsed_millis,
            sub_millis_remainder: Duration::ZERO,
            processed_millis: 0,
            running: true,
        }
    }

    fn advance_by(&mut self, duration: Duration) {
        if !self.running {
            return;
        }

        self.prepare();
        let total_advanced = self
            .sub_millis_remainder
            .checked_add(duration)
            .expect("manual timer duration overflow");
        let advanced_millis =
            u64::try_from(total_advanced.as_millis()).expect("manual timer duration overflow");
        self.sub_millis_remainder = total_advanced
            .checked_sub(Duration::from_millis(advanced_millis))
            .expect("manual timer remainder underflow");
        let target_millis = if advanced_millis == 0 {
            self.current_millis()
        } else {
            self.advance_clock(advanced_millis)
        };
        let ticks_to_process = target_millis.saturating_sub(self.processed_millis);
        self.advance_ticks(ticks_to_process);
        self.prepare();
    }

    fn advance_to_next(&mut self) -> bool {
        if !self.running {
            return false;
        }

        self.prepare();
        loop {
            if !self.running {
                return false;
            }

            match self.core.can_skip() {
                Skip::Empty => return false,
                Skip::Millis(can_skip) if can_skip > 0 => {
                    self.skip_millis(u64::from(can_skip));
                    self.prepare();
                }
                Skip::Millis(_) | Skip::None => {
                    // Once the next entry sits in the primary wheel, `can_skip`
                    // can only promise that something may fire on the next tick,
                    // not which exact future millisecond will do it.
                    if self.advance_one_tick() > 0 {
                        return true;
                    }
                    self.prepare();
                }
            }
        }
    }

    fn prepare(&mut self) {
        if matches!(self.core.drain_messages(), QueueTimerControl::Stop) {
            self.running = false;
        }
    }

    fn current_millis(&self) -> u64 {
        self.elapsed_millis.load(Ordering::Acquire)
    }

    fn advance_clock(&self, advanced_millis: u64) -> u64 {
        let next_millis = self
            .current_millis()
            .checked_add(advanced_millis)
            .expect("manual timer duration overflow");
        self.elapsed_millis.store(next_millis, Ordering::Release);
        next_millis
    }

    fn advance_ticks(&mut self, mut remaining_ticks: u64) {
        while self.running && remaining_ticks > 0 {
            self.prepare();
            if !self.running {
                return;
            }

            match self.core.can_skip() {
                Skip::Empty => {
                    self.processed_millis += remaining_ticks;
                    return;
                }
                Skip::Millis(can_skip) if can_skip > 0 => {
                    let skipped_ticks = remaining_ticks.min(u64::from(can_skip));
                    self.core
                        .skip(u32::try_from(skipped_ticks).expect("skip count fits in u32"));
                    self.processed_millis += skipped_ticks;
                    remaining_ticks -= skipped_ticks;
                }
                Skip::Millis(_) | Skip::None => {
                    self.core.tick();
                    self.processed_millis += 1;
                    remaining_ticks -= 1;
                }
            }
        }
    }

    fn skip_millis(&mut self, skip_millis: u64) {
        if skip_millis == 0 {
            return;
        }

        self.advance_clock(skip_millis);
        self.core
            .skip(u32::try_from(skip_millis).expect("skip count fits in u32"));
        self.processed_millis += skip_millis;
    }

    fn advance_one_tick(&mut self) -> usize {
        debug_assert!(
            self.sub_millis_remainder < Duration::from_millis(1),
            "sub-millisecond remainder must stay below one millisecond"
        );
        self.sub_millis_remainder = Duration::ZERO;
        self.advance_clock(1);
        self.processed_millis += 1;
        self.core.tick()
    }
}

#[cfg(feature = "uuid-extras")]
impl ManualTimer<uuid::Uuid, OneShotClosureState<uuid::Uuid>, PeriodicClosureState<uuid::Uuid>> {
    /// Shorthand for creating a manual timer using `Uuid` identifiers and
    /// closure state.
    pub fn for_uuid_closures() -> Self {
        Self::new()
    }
}

#[cfg(feature = "uuid-extras")]
#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Arc, Mutex};
    use uuid::Uuid;

    #[test]
    fn oneshot_triggers_only_after_manual_advance() {
        let timer = ManualTimer::for_uuid_closures();
        let mut timer_ref = timer.timer_ref();
        let fired = Arc::new(Mutex::new(false));
        let fired_clone = Arc::clone(&fired);

        timer_ref.schedule_action_once(Uuid::new_v4(), Duration::from_millis(5), move |_| {
            let mut guard = fired_clone.lock().unwrap();
            *guard = true;
        });

        timer.advance_by(Duration::from_millis(4));
        assert!(!*fired.lock().unwrap());

        timer.advance_by(Duration::from_millis(1));
        assert!(*fired.lock().unwrap());
    }

    #[test]
    fn cancel_prevents_future_trigger() {
        let timer = ManualTimer::for_uuid_closures();
        let mut timer_ref = timer.timer_ref();
        let fired = Arc::new(Mutex::new(false));
        let fired_clone = Arc::clone(&fired);
        let id = Uuid::new_v4();

        timer_ref.schedule_action_once(id, Duration::from_millis(5), move |_| {
            let mut guard = fired_clone.lock().unwrap();
            *guard = true;
        });
        timer_ref.cancel(&id);

        timer.advance_by(Duration::from_millis(5));
        assert!(!*fired.lock().unwrap());
    }

    #[test]
    fn advance_to_next_triggers_periodic_once_per_call() {
        let timer = ManualTimer::for_uuid_closures();
        let mut timer_ref = timer.timer_ref();
        let fired = Arc::new(Mutex::new(Vec::new()));
        let fired_clone = Arc::clone(&fired);

        timer_ref.schedule_action_periodic(
            Uuid::new_v4(),
            Duration::from_millis(5),
            Duration::from_millis(7),
            move |_| {
                fired_clone.lock().unwrap().push(());
                if fired_clone.lock().unwrap().len() < 3 {
                    TimerReturn::Reschedule(())
                } else {
                    TimerReturn::Cancel
                }
            },
        );

        assert!(timer.advance_to_next());
        assert_eq!(fired.lock().unwrap().len(), 1);
        assert!(timer.advance_to_next());
        assert_eq!(fired.lock().unwrap().len(), 2);
        assert!(timer.advance_to_next());
        assert_eq!(fired.lock().unwrap().len(), 3);
        assert!(!timer.advance_to_next());
    }

    #[test]
    fn timer_ref_now_tracks_manual_advance_at_millisecond_resolution() {
        let timer = ManualTimer::for_uuid_closures();
        let timer_ref = timer.timer_ref();
        let base = timer_ref.now();

        timer.advance_by(Duration::from_micros(999));
        assert_eq!(timer.elapsed(), Duration::ZERO);
        assert_eq!(timer_ref.now(), base);

        timer.advance_by(Duration::from_micros(1));
        assert_eq!(timer.elapsed(), Duration::from_millis(1));
        assert_eq!(
            timer_ref.now().duration_since(base),
            Duration::from_millis(1)
        );
    }

    #[test]
    fn timer_ref_now_inside_handler_is_not_earlier_than_due_time() {
        let timer = ManualTimer::for_uuid_closures();
        let mut timer_ref = timer.timer_ref();
        let scheduled_from = timer_ref.now();
        let delay = Duration::from_millis(5);
        let handler_timer_ref = timer_ref.clone();
        let observed_now = Arc::new(Mutex::new(None));
        let observed_now_clone = Arc::clone(&observed_now);

        timer_ref.schedule_action_once(Uuid::new_v4(), delay, move |_| {
            let now = handler_timer_ref.now();
            *observed_now_clone.lock().unwrap() = Some(now);
        });

        timer.advance_by(Duration::from_millis(20));

        let observed_now = observed_now
            .lock()
            .unwrap()
            .expect("oneshot callback should record observed time");
        assert!(
            observed_now.duration_since(scheduled_from) >= delay,
            "handler observed {observed_now:?}, which is earlier than scheduled lower bound {:?}",
            scheduled_from + delay
        );
    }
}
