use std::{fmt, hash::Hash, time::Duration};

/// Indicate whether or not to reschedule a periodic timer
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TimerReturn<S> {
    /// Reschedule the timer
    Reschedule(S),
    /// Do not reschedule the timer
    Cancel,
}
impl<S> TimerReturn<S> {
    /// Whether or not this timer should be rescheduled
    pub fn should_reschedule(&self) -> bool {
        match self {
            TimerReturn::Reschedule(_) => true,
            TimerReturn::Cancel => false,
        }
    }

    /// Replace the item stored in the `TimerReturn::Reschedule` variant
    /// with the return value of the given function, given the current value
    pub fn map<T, F>(self, f: F) -> TimerReturn<T>
    where
        F: FnOnce(S) -> T,
    {
        match self {
            TimerReturn::Reschedule(s) => TimerReturn::Reschedule(f(s)),
            TimerReturn::Cancel => TimerReturn::Cancel,
        }
    }
}

/// A trait for state that can be triggered once
pub trait OneshotState {
    /// The type of the unique id of the outstanding timeout
    type Id: Hash + Clone + Eq;

    /// A reference to the id associated with this state
    fn id(&self) -> &Self::Id;
    /// Trigger should be called by the timer implementation
    /// when the timeout has expired.
    ///
    /// The method can be used for custom expiry actions,
    /// but it is strongly recommended to keep these quick,
    /// as long actions can delay the execution of later timers.
    fn trigger(self);
}

/// A trait for state that can be triggered more than once once
///
/// This is different from oneshot timers,
/// for the a similar reason to that why the `FnOnce` trait is different from the `Fn` trait.
/// In effect, periodic state needs to be able to produce a new instance of itself for the next
/// period, while oneshot state does not.
pub trait PeriodicState {
    /// The type of the unique id of the outstanding timeout
    type Id: Hash + Clone + Eq;

    /// A reference to the id associated with this state
    fn id(&self) -> &Self::Id;

    /// Trigger should be called by the timer implementation
    /// when the timeout has expired.
    ///
    /// The method can be used for custom expiry actions,
    /// but it is strongly recommended to keep these quick,
    /// as long actions can delay the execution of later timers.
    ///
    /// For periodic actions the trigger actions may mutate (or replace)
    /// the state of the timer entry itself.
    /// Together with the ability to prevent reschedulling, this can be used
    /// to implement "counter"-style timers, that happen a fixed number of times
    /// before being dropped automatically.
    fn trigger(self) -> TimerReturn<Self>
    where
        Self: Sized;
}

/// A concrete entry for an outstanding timeout
#[derive(Debug)]
pub enum TimerEntry<I, O, P>
where
    I: Hash + Clone + Eq,
    O: OneshotState<Id = I>,
    P: PeriodicState<Id = I>,
{
    /// A one-off timer
    OneShot {
        /// The length of the timeout
        timeout: Duration,
        /// The information to store along with the timer
        state: O,
    },
    /// A recurring timer
    Periodic {
        /// The delay until the `action` is first invoked
        delay: Duration,
        /// The time between `action` invocations
        period: Duration,
        /// The information to store along with the timer
        state: P,
    },
}

impl<I, O, P> TimerEntry<I, O, P>
where
    I: Hash + Clone + Eq,
    O: OneshotState<Id = I>,
    P: PeriodicState<Id = I>,
{
    /// A reference to the id associated with this entry
    ///
    /// Equals calling the `id()` function on either state type.
    pub fn id(&self) -> &I {
        match self {
            TimerEntry::OneShot { state, .. } => state.id(),
            TimerEntry::Periodic { state, .. } => state.id(),
        }
    }

    /// Returns the time until the timeout is supposed to be triggered
    pub fn delay(&self) -> &Duration {
        match self {
            TimerEntry::OneShot { timeout, .. } => timeout,
            TimerEntry::Periodic { delay, .. } => delay,
        }
    }
}

/// A basic low-level timer API
///
/// This allows behaviours to be scheduled for later execution.
pub trait Timer {
    /// A type to uniquely identify any timeout to be schedulled or cancelled
    type Id: Hash + Clone + Eq;

    /// The type of state to keep for oneshot timers
    type OneshotState: OneshotState<Id = Self::Id>;

    /// The type of state to keep for periodic timers
    type PeriodicState: PeriodicState<Id = Self::Id>;

    /// Schedule the `state` to be triggered once after the `timeout` expires
    ///
    /// # Note
    ///
    /// Depending on your system and the implementation used,
    /// there is always a certain lag between the triggering of the `state`
    /// and the `timeout` expiring on the system's clock.
    /// Thus it is only guaranteed that the `state` is not triggered *before*
    /// the `timeout` expires, but no bounds on the lag are given.
    fn schedule_once(&mut self, timeout: Duration, state: Self::OneshotState);

    /// Schedule the `state` to be triggered every `timeout` time units
    ///
    /// The first time, the `state` will be trigerreed after `delay` expires,
    /// and then again every `timeout` time units after, unless the
    /// [TimerReturn](TimerReturn) given specifies otherwise.
    ///
    /// # Note
    ///
    /// Depending on your system and the implementation used,
    /// there is always a certain lag between the triggering of the `state`
    /// and the `timeout` expiring on the system's clock.
    /// Thus it is only guaranteed that the `state` is not triggered *before*
    /// the `timeout` expires, but no bounds on the lag are given.
    fn schedule_periodic(&mut self, delay: Duration, period: Duration, state: Self::PeriodicState);

    /// Cancel the timer indicated by the unique `id`
    fn cancel(&mut self, id: &Self::Id);
}

/// A timeout state for a one-shot timer using a closure as the triggering action
pub struct OneShotClosureState<I> {
    /// The id of the timeout state
    id: I,
    /// The action to invoke when the timeout expires
    action: Box<dyn FnOnce(I) + Send + 'static>,
}

impl<I> OneShotClosureState<I> {
    /// Produces a new instance of this state type
    /// from a unique id and the action to be executed
    /// when it expires.
    pub fn new<F>(id: I, action: F) -> Self
    where
        F: FnOnce(I) + Send + 'static,
    {
        OneShotClosureState {
            id,
            action: Box::new(action),
        }
    }
}

#[cfg(feature = "uuid-extras")]
impl OneShotClosureState<uuid::Uuid> {
    /// Produces a new instance of this state type
    /// using a random unique id and the action to be executed
    /// when it expires.
    ///
    /// Uses `Uuid::new_v4()` internally.
    pub fn with_random_id<F>(action: F) -> Self
    where
        F: FnOnce(uuid::Uuid) + Send + 'static,
    {
        Self::new(uuid::Uuid::new_v4(), action)
    }
}

impl<I> OneshotState for OneShotClosureState<I>
where
    I: Hash + Clone + Eq,
{
    type Id = I;

    fn id(&self) -> &Self::Id {
        &self.id
    }

    fn trigger(self) {
        (self.action)(self.id)
    }
}

impl<I> fmt::Debug for OneShotClosureState<I>
where
    I: Hash + Clone + Eq + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "OneShotClosureState(id={:?}, action=<function>)",
            self.id
        )
    }
}

/// A timeout state for a periodic timer using a closure as the triggering action
pub struct PeriodicClosureState<I> {
    /// The id of the timeout state
    id: I,
    /// The action to invoke when the timeout expires
    action: Box<dyn FnMut(I) -> TimerReturn<()> + Send + 'static>,
}

impl<I> PeriodicClosureState<I> {
    /// Produces a new instance of this state type
    /// from a unique id and the action to be executed
    /// every time it expires.
    pub fn new<F>(id: I, action: F) -> Self
    where
        F: FnMut(I) -> TimerReturn<()> + Send + 'static,
    {
        PeriodicClosureState {
            id,
            action: Box::new(action),
        }
    }
}

#[cfg(feature = "uuid-extras")]
impl PeriodicClosureState<uuid::Uuid> {
    /// Produces a new instance of this state type
    /// using a random unique id and the action to be executed
    /// every time it expires.
    ///
    /// Uses `Uuid::new_v4()` internally.
    pub fn with_random_id<F>(action: F) -> Self
    where
        F: FnMut(uuid::Uuid) -> TimerReturn<()> + Send + 'static,
    {
        Self::new(uuid::Uuid::new_v4(), action)
    }
}

impl<I> PeriodicState for PeriodicClosureState<I>
where
    I: Hash + Clone + Eq,
{
    type Id = I;

    fn id(&self) -> &Self::Id {
        &self.id
    }

    fn trigger(mut self) -> TimerReturn<Self>
    where
        Self: Sized,
    {
        let res = (self.action)(self.id.clone());
        res.map(|_| self)
    }
}

impl<I> fmt::Debug for PeriodicClosureState<I>
where
    I: Hash + Clone + Eq + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "PeriodicClosureState(id={:?}, action=<function>)",
            self.id
        )
    }
}

/// This trait is a convenience API for [timers](Timer) that use the closure state types,
/// i.e. [OneShotClosureState](OneShotClosureState) and [PeriodicClosureState](PeriodicClosureState).
pub trait ClosureTimer: Timer {
    /// Schedule the `action` to be executed once after the `timeout` expires
    ///
    /// # Note
    ///
    /// Depending on your system and the implementation used,
    /// there is always a certain lag between the execution of the `action`
    /// and the `timeout` expiring on the system's clock.
    /// Thus it is only guaranteed that the `action` is not run *before*
    /// the `timeout` expires, but no bounds on the lag are given.
    fn schedule_action_once<F>(&mut self, id: Self::Id, timeout: Duration, action: F)
    where
        F: FnOnce(Self::Id) + Send + 'static;

    /// Schedule the `action` to be run every `timeout` time units
    ///
    /// The first time, the `action` will be run after `delay` expires,
    /// and then again every `timeout` time units after.
    ///
    /// # Note
    ///
    /// Depending on your system and the implementation used,
    /// there is always a certain lag between the execution of the `action`
    /// and the `timeout` expiring on the system's clock.
    /// Thus it is only guaranteed that the `action` is not run *before*
    /// the `timeout` expires, but no bounds on the lag are given.
    fn schedule_action_periodic<F>(
        &mut self,
        id: Self::Id,
        delay: Duration,
        period: Duration,
        action: F,
    ) where
        F: FnMut(Self::Id) -> TimerReturn<()> + Send + 'static;
}

impl<I, T> ClosureTimer for T
where
    I: Hash + Clone + Eq,
    T: Timer<
        Id = I,
        OneshotState = OneShotClosureState<I>,
        PeriodicState = PeriodicClosureState<I>,
    >,
{
    fn schedule_action_once<F>(&mut self, id: Self::Id, timeout: Duration, action: F)
    where
        F: FnOnce(Self::Id) + Send + 'static,
    {
        self.schedule_once(timeout, OneShotClosureState::new(id, action))
    }

    fn schedule_action_periodic<F>(
        &mut self,
        id: Self::Id,
        delay: Duration,
        period: Duration,
        action: F,
    ) where
        F: FnMut(Self::Id) -> TimerReturn<()> + Send + 'static,
    {
        self.schedule_periodic(delay, period, PeriodicClosureState::new(id, action))
    }
}
