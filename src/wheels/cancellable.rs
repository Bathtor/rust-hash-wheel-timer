use super::*;
use crate::wheels::quad_wheel::{
    PruneDecision,
    QuadWheelWithOverflow as BasicQuadWheelWithOverflow,
};
#[cfg(feature = "fnv")]
use fnv::FnvHashMap;
#[cfg(not(feature = "fnv"))]
use std::collections::HashMap;

/// A trait for timer entries that can be uniquely identified, so they can be cancelled
pub trait CancellableTimerEntry: Debug {
    /// The type of the unique id of the outstanding timeout
    type Id: Hash + Clone + Eq;

    /// Returns the unique id of the outstanding timeout
    fn id(&self) -> &Self::Id;
}

/// A pruner implementation for [Weak](std::rc::Weak) references
///
/// Keeps values that can still be upgraded.
pub fn rc_prune<E>(e: &Weak<E>) -> PruneDecision {
    if e.strong_count() > 0 {
        PruneDecision::Keep
    } else {
        PruneDecision::Drop
    }
}

/// An implementation of four-level byte-sized wheel
///
/// Any value scheduled so far off that it doesn't fit into the wheel
/// is stored in an overflow `Vec` and added to the wheel, once time as advanced enough
/// that it actually fits.
/// In this design the maximum schedule duration for the wheel itself is [`u32::MAX`](std::u32::MAX) units (typically ms),
/// everything else goes into the overflow `Vec`.
pub struct QuadWheelWithOverflow<EntryType>
where
    EntryType: CancellableTimerEntry,
{
    wheel: BasicQuadWheelWithOverflow<Weak<EntryType>>,
    #[cfg(feature = "fnv")]
    timers: FnvHashMap<EntryType::Id, Rc<EntryType>>,
    #[cfg(not(feature = "fnv"))]
    timers: HashMap<EntryType::Id, Rc<EntryType>>,
}

impl<EntryType> QuadWheelWithOverflow<EntryType>
where
    EntryType: TimerEntryWithDelay + CancellableTimerEntry,
{
    /// Insert a new timeout into the wheel
    pub fn insert(&mut self, e: EntryType) -> Result<(), TimerError<EntryType>> {
        self.insert_ref(Rc::new(e)).map_err(|err| match err {
            TimerError::Expired(rc_e) => {
                let e = Rc::try_unwrap(rc_e).unwrap(); // No one except us should have references as this point, so this should be safe
                TimerError::Expired(e)
            }
            TimerError::NotFound => TimerError::NotFound,
        })
    }

    /// Insert a new timeout into the wheel
    pub fn insert_ref(&mut self, e: Rc<EntryType>) -> Result<(), TimerError<Rc<EntryType>>> {
        let delay = e.delay();
        self.insert_ref_with_delay(e, delay)
    }
}

impl<EntryType> QuadWheelWithOverflow<EntryType>
where
    EntryType: CancellableTimerEntry,
{
    /// Create a new wheel
    pub fn new() -> Self {
        QuadWheelWithOverflow {
            wheel: BasicQuadWheelWithOverflow::new(rc_prune::<EntryType>),
            #[cfg(feature = "fnv")]
            timers: FnvHashMap::default(),
            #[cfg(not(feature = "fnv"))]
            timers: HashMap::new(),
        }
    }

    /// Insert a new timeout into the wheel to be returned after `delay` ticks
    pub fn insert_ref_with_delay(
        &mut self,
        e: Rc<EntryType>,
        delay: Duration,
    ) -> Result<(), TimerError<Rc<EntryType>>> {
        let weak_e = Rc::downgrade(&e);

        match self.wheel.insert_ref_with_delay(weak_e, delay) {
            Ok(_) => {
                self.timers.insert(e.id().clone(), e);
                Ok(())
            }
            Err(TimerError::Expired(_weak_e)) => Err(TimerError::Expired(e)),
            Err(TimerError::NotFound) => Err(TimerError::NotFound), // not that this can happen here, but it makes the compiler happy
        }
    }

    /// Cancel the timeout with the given `id`
    ///
    /// This method is very cheap, as it doesn't actually touch the wheels at all.
    /// It simply removes the value from the lookup table, so it can't be executed
    /// once its triggered. This also automatically prevents rescheduling of periodic timeouts.
    pub fn cancel(&mut self, id: &EntryType::Id) -> Result<(), TimerError<Infallible>> {
        // Simply remove it from the lookup table
        // This will prevent the Weak pointer in the wheels from upgrading later
        match self.timers.remove_entry(id) {
            Some(_) => Ok(()),
            None => Err(TimerError::NotFound),
        }
    }

    fn take_timer(&mut self, weak_e: Weak<EntryType>) -> Option<Rc<EntryType>> {
        match weak_e.upgrade() {
            Some(rc_e) => {
                match self.timers.remove_entry(rc_e.id()) {
                    Some(rc_e2) => drop(rc_e2), // ok
                    None => panic!("TimerEntry was upgraded but not in timers list!"),
                }
                Some(rc_e)
            }
            None => None,
        }
    }

    /// Move the wheel forward by a single unit (ms)
    ///
    /// Returns a list of all timers that expire during this tick.
    pub fn tick(&mut self) -> Vec<Rc<EntryType>> {
        let res = self.wheel.tick();
        res.into_iter()
            .flat_map(|weak_e| self.take_timer(weak_e))
            .collect()
    }

    /// Skip a certain `amount` of units (ms)
    ///
    /// No timers will be executed for the skipped time.
    /// Only use this after determining that it's actually
    /// valid with [can_skip](QuadWheelWithOverflow::can_skip)!
    pub fn skip(&mut self, amount: u32) -> () {
        self.wheel.skip(amount);
    }

    /// Determine if and how many ticks can be skipped
    pub fn can_skip(&self) -> Skip {
        self.wheel.can_skip()
    }
}

#[cfg(feature = "uuid-extras")]
#[cfg(test)]
mod uuid_tests {
    use super::*;
    use crate::UuidOnlyTimerEntry;
    use uuid::Uuid;

    #[test]
    fn single_schedule_fail() {
        let mut timer = QuadWheelWithOverflow::new();
        let id = Uuid::new_v4();
        let res = timer.insert(IdOnlyTimerEntry {
            id,
            delay: Duration::from_millis(0),
        });
        assert!(res.is_err());
        match res {
            Err(TimerError::Expired(e)) => assert_eq!(e.id(), &id),
            _ => panic!("Unexpected result {:?}", res),
        }
    }

    #[test]
    fn single_ms_schedule() {
        let mut timer = QuadWheelWithOverflow::new();
        let id = Uuid::new_v4();
        timer
            .insert(UuidOnlyTimerEntry {
                id,
                delay: Duration::from_millis(1),
            })
            .expect("Could not insert timer entry!");
        let res = timer.tick();
        assert_eq!(res.len(), 1);
        assert_eq!(res[0].id(), &id);
    }

    #[test]
    fn single_ms_cancel() {
        let mut timer = QuadWheelWithOverflow::new();
        let id = Uuid::new_v4();
        timer
            .insert(UuidOnlyTimerEntry {
                id,
                delay: Duration::from_millis(1),
            })
            .expect("Could not insert timer entry!");
        timer.cancel(&id).expect("Entry could not be cancelled!");
        let res = timer.tick();
        assert_eq!(res.len(), 0);
    }

    #[test]
    fn single_ms_reschedule() {
        let mut timer = QuadWheelWithOverflow::new();
        let id = Uuid::new_v4();
        let entry = UuidOnlyTimerEntry {
            id,
            delay: Duration::from_millis(1),
        };

        timer.insert(entry).expect("Could not insert timer entry!");
        for _ in 0..1000 {
            let mut res = timer.tick();
            assert_eq!(res.len(), 1);
            let entry = res.pop().unwrap();
            assert_eq!(entry.id(), &id);
            timer
                .insert_ref(entry)
                .expect("Could not insert timer entry!");
        }
    }

    #[test]
    fn increasing_schedule_no_overflow() {
        let mut timer = QuadWheelWithOverflow::new();
        let mut ids: [Uuid; 25] = [Uuid::nil(); 25];
        for i in 0..=24 {
            let timeout: u64 = 1 << i;
            let id = Uuid::new_v4();
            ids[i] = id;
            let entry = UuidOnlyTimerEntry {
                id,
                delay: Duration::from_millis(timeout),
            };
            timer.insert(entry).expect("Could not insert timer entry!");
        }
        //let mut tick_counter = 0u128;
        for i in 0..=24 {
            let target: u64 = 1 << i;
            let prev: u64 = if i == 0 { 0 } else { 1 << (i - 1) };
            println!("target={} and prev={}", target, prev);
            for _ in (prev + 1)..target {
                let res = timer.tick();
                //tick_counter += 1;
                //println!("Ticked to {}", tick_counter);
                assert_eq!(res.len(), 0);
            }
            let mut res = timer.tick();
            //tick_counter += 1;
            //println!("Ticked to {}", tick_counter);
            assert_eq!(res.len(), 1);
            let entry = res.pop().unwrap();
            assert_eq!(entry.id(), &ids[i]);
        }
    }

    #[test]
    fn increasing_schedule_overflow() {
        let mut timer = QuadWheelWithOverflow::new();
        let mut ids: [Uuid; 33] = [Uuid::nil(); 33];
        for i in 0..=32 {
            let timeout: u64 = 1 << i;
            let id = Uuid::new_v4();
            ids[i] = id;
            let entry = UuidOnlyTimerEntry {
                id,
                delay: Duration::from_millis(timeout),
            };
            timer.insert(entry).expect("Could not insert timer entry!");
        }
        //let mut tick_counter = 0u128;
        for i in 0..=32 {
            let target: u64 = 1 << i;
            let prev: u64 = if i == 0 { 0 } else { 1 << (i - 1) };
            println!("target={} (2^{}) and prev={}", target, i, prev);
            let diff = (target - prev - 1) as u32;
            timer.skip(diff);
            let mut res = timer.tick();
            //tick_counter += 1;
            //println!("Ticked to {}", tick_counter);
            //println!("In slot {} got {} expected {}", target, res.len(), 1);
            assert_eq!(res.len(), 1);
            let entry = res.pop().unwrap();
            assert_eq!(entry.id(), &ids[i]);
        }
    }

    #[test]
    fn increasing_skip() {
        let mut timer = QuadWheelWithOverflow::new();
        let mut ids: [Uuid; 33] = [Uuid::nil(); 33];
        let mut timeouts: [u128; 33] = [0; 33];
        for i in 0..=32 {
            let timeout: u64 = 1 << i;
            timeouts[i] = timeout as u128;
            let id = Uuid::new_v4();
            ids[i] = id;
            let entry = UuidOnlyTimerEntry {
                id,
                delay: Duration::from_millis(timeout),
            };
            timer.insert(entry).expect("Could not insert timer entry!");
            println!("Added timeout at index={} with time={}", i, timeout);
        }
        let mut index = 0usize;
        let mut millis = 0u128;
        while index < 33 {
            match timer.can_skip() {
                Skip::Empty => panic!(
                    "Timer ran empty with index={} and millis={}!",
                    index, millis
                ),
                Skip::Millis(skip) => {
                    timer.skip(skip);
                    millis += skip as u128;
                    println!("Skipped {}ms to {}", skip, millis);
                }
                Skip::None => (),
            }
            let mut res = timer.tick();
            millis += 1u128;
            //println!("Ticked to {}", millis);
            if !res.is_empty() {
                let entry = res.pop().unwrap();
                assert_eq!(entry.id(), &ids[index]);
                assert_eq!(millis, timeouts[index]);
                println!("Handled timeout {} at {}ms", index, millis);
                index += 1usize;
            } else {
                () // ignore empty ticks, which must be done do advance within a wheel
                   //println!("Empty tick at {}ms", millis);
            }
        }
        assert_eq!(timer.can_skip(), Skip::Empty);
    }
}

#[cfg(test)]
mod u64_tests {
    use super::*;

    #[test]
    fn single_schedule_fail() {
        let mut timer = QuadWheelWithOverflow::new();
        let id = 1u64;
        let res = timer.insert(IdOnlyTimerEntry {
            id,
            delay: Duration::from_millis(0),
        });
        assert!(res.is_err());
        match res {
            Err(TimerError::Expired(e)) => assert_eq!(e.id(), &id),
            _ => panic!("Unexpected result {:?}", res),
        }
    }

    #[test]
    fn single_ms_schedule() {
        let mut timer = QuadWheelWithOverflow::new();
        let id = 1u64;
        timer
            .insert(IdOnlyTimerEntry {
                id,
                delay: Duration::from_millis(1),
            })
            .expect("Could not insert timer entry!");
        let res = timer.tick();
        assert_eq!(res.len(), 1);
        assert_eq!(res[0].id(), &id);
    }

    #[test]
    fn single_ms_cancel() {
        let mut timer = QuadWheelWithOverflow::new();
        let id = 1u64;
        timer
            .insert(IdOnlyTimerEntry {
                id,
                delay: Duration::from_millis(1),
            })
            .expect("Could not insert timer entry!");
        timer.cancel(&id).expect("Entry could not be cancelled!");
        let res = timer.tick();
        assert_eq!(res.len(), 0);
    }

    #[test]
    fn single_ms_reschedule() {
        let mut timer = QuadWheelWithOverflow::new();
        let id = 1u64;
        let entry = IdOnlyTimerEntry {
            id,
            delay: Duration::from_millis(1),
        };

        timer.insert(entry).expect("Could not insert timer entry!");
        for _ in 0..1000 {
            let mut res = timer.tick();
            assert_eq!(res.len(), 1);
            let entry = res.pop().unwrap();
            assert_eq!(entry.id(), &id);
            timer
                .insert_ref(entry)
                .expect("Could not insert timer entry!");
        }
    }

    #[test]
    fn increasing_schedule_no_overflow() {
        let mut timer = QuadWheelWithOverflow::new();
        let mut ids: [u64; 25] = [0; 25];
        for i in 0..=24 {
            let timeout: u64 = 1 << i;
            let id = i as u64;
            ids[i] = id;
            let entry = IdOnlyTimerEntry {
                id,
                delay: Duration::from_millis(timeout),
            };
            timer.insert(entry).expect("Could not insert timer entry!");
        }
        //let mut tick_counter = 0u128;
        for i in 0..=24 {
            let target: u64 = 1 << i;
            let prev: u64 = if i == 0 { 0 } else { 1 << (i - 1) };
            println!("target={} and prev={}", target, prev);
            for _ in (prev + 1)..target {
                let res = timer.tick();
                //tick_counter += 1;
                //println!("Ticked to {}", tick_counter);
                assert_eq!(res.len(), 0);
            }
            let mut res = timer.tick();
            //tick_counter += 1;
            //println!("Ticked to {}", tick_counter);
            assert_eq!(res.len(), 1);
            let entry = res.pop().unwrap();
            assert_eq!(entry.id(), &ids[i]);
        }
    }

    #[test]
    fn increasing_schedule_overflow() {
        let mut timer = QuadWheelWithOverflow::new();
        let mut ids: [u64; 33] = [0; 33];
        for i in 0..=32 {
            let timeout: u64 = 1 << i;
            let id = i as u64;
            ids[i] = id;
            let entry = IdOnlyTimerEntry {
                id,
                delay: Duration::from_millis(timeout),
            };
            timer.insert(entry).expect("Could not insert timer entry!");
        }
        //let mut tick_counter = 0u128;
        for i in 0..=32 {
            let target: u64 = 1 << i;
            let prev: u64 = if i == 0 { 0 } else { 1 << (i - 1) };
            println!("target={} (2^{}) and prev={}", target, i, prev);
            let diff = (target - prev - 1) as u32;
            timer.skip(diff);
            let mut res = timer.tick();
            //tick_counter += 1;
            //println!("Ticked to {}", tick_counter);
            //println!("In slot {} got {} expected {}", target, res.len(), 1);
            assert_eq!(res.len(), 1);
            let entry = res.pop().unwrap();
            assert_eq!(entry.id(), &ids[i]);
        }
    }

    #[test]
    fn increasing_skip() {
        let mut timer = QuadWheelWithOverflow::new();
        let mut ids: [u64; 33] = [0; 33];
        let mut timeouts: [u128; 33] = [0; 33];
        for i in 0..=32 {
            let timeout: u64 = 1 << i;
            timeouts[i] = timeout as u128;
            let id = i as u64;
            ids[i] = id;
            let entry = IdOnlyTimerEntry {
                id,
                delay: Duration::from_millis(timeout),
            };
            timer.insert(entry).expect("Could not insert timer entry!");
            println!("Added timeout at index={} with time={}", i, timeout);
        }
        let mut index = 0usize;
        let mut millis = 0u128;
        while index < 33 {
            match timer.can_skip() {
                Skip::Empty => panic!(
                    "Timer ran empty with index={} and millis={}!",
                    index, millis
                ),
                Skip::Millis(skip) => {
                    timer.skip(skip);
                    millis += skip as u128;
                    println!("Skipped {}ms to {}", skip, millis);
                }
                Skip::None => (),
            }
            let mut res = timer.tick();
            millis += 1u128;
            //println!("Ticked to {}", millis);
            if !res.is_empty() {
                let entry = res.pop().unwrap();
                assert_eq!(entry.id(), &ids[index]);
                assert_eq!(millis, timeouts[index]);
                println!("Handled timeout {} at {}ms", index, millis);
                index += 1usize;
            } else {
                () // ignore empty ticks, which must be done do advance within a wheel
                   //println!("Empty tick at {}ms", millis);
            }
        }
        assert_eq!(timer.can_skip(), Skip::Empty);
    }
}
