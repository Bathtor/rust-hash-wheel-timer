use super::*;
use crate::wheels::{cancellable::*, *};
use crossbeam_channel as channel;
use std::{
    fmt,
    hash::Hash,
    rc::Rc,
    sync::{
        atomic::{AtomicU64, Ordering},
        Arc,
    },
    time::{Duration, Instant},
};

#[derive(Debug)]
pub(crate) enum TimerMsg<I, O, P>
where
    I: Hash + Clone + Eq,
    O: OneshotState<Id = I>,
    P: PeriodicState<Id = I>,
{
    Schedule(TimerEntry<I, O, P>),
    Cancel(I),
    Stop,
}

/// A shareable scheduling handle for queue-backed timer drivers.
///
/// This handle is used by both the threaded and manually-driven timers in this crate.
pub struct TimerRef<I, O, P>
where
    I: Hash + Clone + Eq,
    O: OneshotState<Id = I>,
    P: PeriodicState<Id = I>,
{
    work_queue: channel::Sender<TimerMsg<I, O, P>>,
    clock: ClockRef,
}

impl<I, O, P> TimerRef<I, O, P>
where
    I: Hash + Clone + Eq,
    O: OneshotState<Id = I>,
    P: PeriodicState<Id = I>,
{
    pub(crate) fn new(work_queue: channel::Sender<TimerMsg<I, O, P>>, clock: ClockRef) -> Self {
        Self { work_queue, clock }
    }

    /// Returns the current time according to the underlying timer driver.
    ///
    /// For the threaded timer this is wall-clock time. For the manual timer
    /// this advances only when the caller explicitly advances the timer.
    ///
    /// When called from a timeout handler, the returned instant is guaranteed
    /// not to be earlier than the timeout deadline that permitted the handler
    /// to run, but it may be later because timeout delivery itself can lag
    /// behind the nominal deadline.
    pub fn now(&self) -> Instant {
        self.clock.now()
    }
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

    fn schedule_once(&mut self, timeout: Duration, state: Self::OneshotState) {
        let entry = TimerEntry::OneShot { timeout, state };
        self.work_queue
            .send(TimerMsg::Schedule(entry))
            .unwrap_or_else(|error| eprintln!("Could not send Schedule msg: {:?}", error));
    }

    fn schedule_periodic(&mut self, delay: Duration, period: Duration, state: Self::PeriodicState) {
        let entry = TimerEntry::Periodic {
            delay,
            period,
            state,
        };
        self.work_queue
            .send(TimerMsg::Schedule(entry))
            .unwrap_or_else(|error| eprintln!("Could not send Schedule msg: {:?}", error));
    }

    fn cancel(&mut self, id: &Self::Id) {
        self.work_queue
            .send(TimerMsg::Cancel(id.clone()))
            .unwrap_or_else(|error| eprintln!("Could not send Cancel msg: {:?}", error));
    }
}

impl<I, O, P> Clone for TimerRef<I, O, P>
where
    I: Hash + Clone + Eq,
    O: OneshotState<Id = I>,
    P: PeriodicState<Id = I>,
{
    fn clone(&self) -> Self {
        Self {
            work_queue: self.work_queue.clone(),
            clock: self.clock.clone(),
        }
    }
}

/// Non-blocking clock source shared with queue-backed timer handles.
///
/// The manual variant stores logical time as an atomic elapsed offset from a
/// fixed base instant so component threads can read the current timer-aligned
/// instant without taking the manual timer's mutex.
#[derive(Clone, Debug)]
pub(crate) enum ClockRef {
    Realtime,
    Manual {
        base: Instant,
        elapsed_millis: Arc<AtomicU64>,
    },
}

impl ClockRef {
    pub(crate) fn realtime() -> Self {
        Self::Realtime
    }

    pub(crate) fn manual(base: Instant, elapsed_millis: Arc<AtomicU64>) -> Self {
        Self::Manual {
            base,
            elapsed_millis,
        }
    }

    fn now(&self) -> Instant {
        match self {
            Self::Realtime => Instant::now(),
            Self::Manual {
                base,
                elapsed_millis,
            } => {
                let elapsed = elapsed_millis.load(Ordering::Acquire);
                base.checked_add(Duration::from_millis(elapsed))
                    .expect("manual timer instant overflow")
            }
        }
    }
}

#[derive(Debug)]
pub(crate) enum QueueTimerControl {
    Continue,
    Stop,
}

#[derive(Debug)]
enum QueueTimerEntry<I, O, P>
where
    I: Hash + Clone + Eq,
    O: OneshotState<Id = I>,
    P: PeriodicState<Id = I>,
{
    OneShot { state: O },
    Periodic { period: Duration, state: P },
}

impl<I, O, P> QueueTimerEntry<I, O, P>
where
    I: Hash + Clone + Eq + fmt::Debug,
    O: OneshotState<Id = I> + fmt::Debug,
    P: PeriodicState<Id = I> + fmt::Debug,
{
    fn from_timer_entry(entry: TimerEntry<I, O, P>) -> (Self, Duration) {
        match entry {
            TimerEntry::OneShot { timeout, state } => {
                let queue_entry = QueueTimerEntry::OneShot { state };
                (queue_entry, timeout)
            }
            TimerEntry::Periodic {
                delay,
                period,
                state,
            } => {
                let queue_entry = QueueTimerEntry::Periodic { period, state };
                (queue_entry, delay)
            }
        }
    }

    fn execute(self) -> Option<(Self, Duration)> {
        match self {
            QueueTimerEntry::OneShot { state } => {
                state.trigger();
                None
            }
            QueueTimerEntry::Periodic { period, state } => match state.trigger() {
                TimerReturn::Reschedule(new_state) => {
                    let new_entry = QueueTimerEntry::Periodic {
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
        unique
            .execute()
            .map(|(new_unique, delay)| (Rc::new(new_unique), delay))
    }
}

impl<I, O, P> CancellableTimerEntry for QueueTimerEntry<I, O, P>
where
    I: Hash + Clone + Eq + fmt::Debug,
    O: OneshotState<Id = I> + fmt::Debug,
    P: PeriodicState<Id = I> + fmt::Debug,
{
    type Id = I;

    fn id(&self) -> &Self::Id {
        match self {
            QueueTimerEntry::OneShot { state } => state.id(),
            QueueTimerEntry::Periodic { state, .. } => state.id(),
        }
    }
}

pub(crate) struct QueueTimerCore<I, O, P>
where
    I: Hash + Clone + Eq + fmt::Debug,
    O: OneshotState<Id = I> + fmt::Debug,
    P: PeriodicState<Id = I> + fmt::Debug,
{
    timer: QuadWheelWithOverflow<QueueTimerEntry<I, O, P>>,
    work_queue: channel::Receiver<TimerMsg<I, O, P>>,
}

impl<I, O, P> QueueTimerCore<I, O, P>
where
    I: Hash + Clone + Eq + fmt::Debug,
    O: OneshotState<Id = I> + fmt::Debug,
    P: PeriodicState<Id = I> + fmt::Debug,
{
    pub(crate) fn new(work_queue: channel::Receiver<TimerMsg<I, O, P>>) -> Self {
        Self {
            timer: QuadWheelWithOverflow::new(),
            work_queue,
        }
    }

    pub(crate) fn work_queue(&self) -> &channel::Receiver<TimerMsg<I, O, P>> {
        &self.work_queue
    }

    pub(crate) fn try_recv(&self) -> Result<TimerMsg<I, O, P>, channel::TryRecvError> {
        self.work_queue.try_recv()
    }

    pub(crate) fn recv(&self) -> Result<TimerMsg<I, O, P>, channel::RecvError> {
        self.work_queue.recv()
    }

    pub(crate) fn drain_messages(&mut self) -> QueueTimerControl {
        loop {
            match self.work_queue.try_recv() {
                Ok(message) => {
                    if matches!(self.handle_msg(message), QueueTimerControl::Stop) {
                        return QueueTimerControl::Stop;
                    }
                }
                Err(channel::TryRecvError::Empty) => return QueueTimerControl::Continue,
                Err(channel::TryRecvError::Disconnected) => {
                    panic!("Timer work_queue unexpectedly shut down!")
                }
            }
        }
    }

    pub(crate) fn handle_msg(&mut self, message: TimerMsg<I, O, P>) -> QueueTimerControl {
        match message {
            TimerMsg::Stop => QueueTimerControl::Stop,
            TimerMsg::Schedule(entry) => {
                let (queue_entry, delay) = QueueTimerEntry::from_timer_entry(entry);
                match self
                    .timer
                    .insert_ref_with_delay(Rc::new(queue_entry), delay)
                {
                    Ok(_) => {}
                    Err(TimerError::Expired(entry)) => {
                        self.trigger_entry(entry);
                    }
                    Err(error) => panic!("Could not insert timer entry! {:?}", error),
                }
                QueueTimerControl::Continue
            }
            TimerMsg::Cancel(id) => {
                match self.timer.cancel(&id) {
                    Ok(_) => {}
                    Err(TimerError::NotFound) => {}
                    Err(error) => panic!("Unexpected error cancelling timer! {:?}", error),
                }
                QueueTimerControl::Continue
            }
        }
    }

    pub(crate) fn can_skip(&self) -> Skip {
        self.timer.can_skip()
    }

    pub(crate) fn is_idle(&self) -> bool {
        self.work_queue.is_empty() && matches!(self.timer.can_skip(), Skip::Empty)
    }

    pub(crate) fn skip(&mut self, amount: u32) {
        self.timer.skip(amount);
    }

    pub(crate) fn tick(&mut self) -> usize {
        let expired = self.timer.tick();
        let expired_count = expired.len();
        for entry in expired {
            self.trigger_entry(entry);
        }
        expired_count
    }

    fn trigger_entry(&mut self, entry: Rc<QueueTimerEntry<I, O, P>>) {
        if let Some((new_entry, delay)) = QueueTimerEntry::execute_unique_ref(entry) {
            match self.timer.insert_ref_with_delay(new_entry, delay) {
                Ok(_) => {}
                Err(TimerError::Expired(entry)) => panic!(
                    "Trying to insert periodic timer entry with 0ms period! {:?}",
                    entry
                ),
                Err(error) => panic!("Could not insert timer entry! {:?}", error),
            }
        }
    }
}
