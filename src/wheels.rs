use super::*;
use arr_macro::arr;
#[cfg(feature = "fnv")]
use fnv::FnvHashMap;
use std::{
    cmp::Eq,
    convert::Infallible,
    fmt::Debug,
    hash::Hash,
    mem,
    rc::{Rc, Weak},
    time::Duration,
    u32,
};

#[cfg(not(feature = "fnv"))]
use std::collections::HashMap;

// trait TimeWheel<IndexType> {
//     fn tick(&mut self, results: &mut TimerList) -> IndexType;
// }

/// A trait for timer entries that can be uniquely identified, so they can be cancelled
pub trait CancellableTimerEntry: Debug {
    /// The type of the unique id of the outstanding timeout
    type Id: Hash + Clone + Eq;

    /// Returns the unique id of the outstanding timeout
    fn id(&self) -> &Self::Id;
}

/// A trait for timer entries that store their delay along the with the state
pub trait TimerEntryWithDelay: CancellableTimerEntry {
    /// Returns the time until the timeout is supposed to be triggered
    fn delay(&self) -> Duration;
}

struct WheelEntry<EntryType, RestType> {
    entry: Weak<EntryType>,
    rest: RestType,
}

type WheelEntryList<EntryType, RestType> = Vec<WheelEntry<EntryType, RestType>>;

struct ByteWheel<EntryType, RestType> {
    slots: [Option<WheelEntryList<EntryType, RestType>>; 256],
    count: u64,
    current: u8,
}

impl<EntryType, RestType> ByteWheel<EntryType, RestType> {
    fn new() -> Self {
        let slots: [Option<WheelEntryList<EntryType, RestType>>; 256] = arr![Option::None; 256];
        ByteWheel {
            slots,
            count: 0,
            current: 0,
        }
    }

    fn insert(&mut self, pos: u8, e: Weak<EntryType>, r: RestType) -> () {
        let index = pos as usize;
        let we = WheelEntry { entry: e, rest: r };
        if self.slots[index].is_none() {
            let l = Vec::new();
            let bl = Some(l);
            self.slots[index] = bl;
        }
        if let Some(ref mut l) = &mut self.slots[index] {
            l.push(we);
            self.count += 1;
        }
    }

    fn is_empty(&self) -> bool {
        self.count == 0
    }

    fn tick(&mut self, results: &mut WheelEntryList<EntryType, RestType>) -> u8 {
        self.current = self.current.wrapping_add(1u8);
        let index = self.current as usize;
        let cur = self.slots[index].take(); //mem::replace(&mut self.slots[index], None);
        match cur {
            Some(mut l) => {
                self.count -= l.len() as u64;
                results.append(l.as_mut());
            }
            None => (), // nothing to do
        }
        self.current
    }
}

struct OverflowEntry<EntryType> {
    entry: Weak<EntryType>,
    remaining_delay: Duration,
}
impl<EntryType> OverflowEntry<EntryType> {
    fn new(entry: Weak<EntryType>, remaining_delay: Duration) -> Self {
        OverflowEntry {
            entry,
            remaining_delay,
        }
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
    primary: ByteWheel<EntryType, [u8; 0]>,
    secondary: ByteWheel<EntryType, [u8; 1]>,
    tertiary: ByteWheel<EntryType, [u8; 2]>,
    quarternary: ByteWheel<EntryType, [u8; 3]>,
    overflow: Vec<OverflowEntry<EntryType>>,
    #[cfg(feature = "fnv")]
    timers: FnvHashMap<EntryType::Id, Rc<EntryType>>,
    #[cfg(not(feature = "fnv"))]
    timers: HashMap<EntryType::Id, Rc<EntryType>>,
}

const MAX_SCHEDULE_DUR: Duration = Duration::from_millis(u32::MAX as u64);
const CYCLE_LENGTH: u64 = 1 << 32; // 2^32
const PRIMARY_LENGTH: u32 = 1 << 8; // 2^8
const SECONDARY_LENGTH: u32 = 1 << 16; // 2^16
const TERTIARY_LENGTH: u32 = 1 << 24; // 2^24

impl<EntryType> QuadWheelWithOverflow<EntryType>
where
    EntryType: TimerEntryWithDelay,
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
            primary: ByteWheel::new(),
            secondary: ByteWheel::new(),
            tertiary: ByteWheel::new(),
            quarternary: ByteWheel::new(),
            overflow: Vec::new(),
            #[cfg(feature = "fnv")]
            timers: FnvHashMap::default(),
            #[cfg(not(feature = "fnv"))]
            timers: HashMap::new(),
        }
    }

    fn remaining_time_in_cycle(&self) -> u64 {
        CYCLE_LENGTH - (self.current_time_in_cycle() as u64)
    }

    fn current_time_in_cycle(&self) -> u32 {
        let time_bytes = [
            self.quarternary.current,
            self.tertiary.current,
            self.secondary.current,
            self.primary.current,
        ];
        u32::from_be(unsafe { mem::transmute(time_bytes) })
    }

    fn insert_timer_ref(&mut self, e: Rc<EntryType>) -> Weak<EntryType> {
        let weak_e = Rc::downgrade(&e);
        self.timers.insert(e.id().clone(), e);
        weak_e
    }

    /// Insert a new timeout into the wheel to be returned after `delay` ticks
    pub fn insert_ref_with_delay(
        &mut self,
        e: Rc<EntryType>,
        delay: Duration,
    ) -> Result<(), TimerError<Rc<EntryType>>> {
        if delay >= MAX_SCHEDULE_DUR {
            let remaining_delay = Duration::from_millis(self.remaining_time_in_cycle());
            let new_delay = delay - remaining_delay;
            let weak_e = self.insert_timer_ref(e);
            let overflow_e = OverflowEntry::new(weak_e, new_delay);
            self.overflow.push(overflow_e);
            Ok(())
        } else {
            let delay = {
                let s = (delay.as_secs() * 1000) as u32;
                let ms = delay.subsec_millis();
                s + ms
            };
            let current_time = self.current_time_in_cycle();
            let absolute_time = delay.wrapping_add(current_time);
            let absolute_bytes: [u8; 4] = unsafe { mem::transmute(absolute_time.to_be()) };
            let zero_time = absolute_time ^ current_time; // a-b%2
            let zero_bytes: [u8; 4] = unsafe { mem::transmute(zero_time.to_be()) };
            match zero_bytes {
                [0, 0, 0, 0] => Err(TimerError::Expired(e)),
                [0, 0, 0, _] => {
                    let weak_e = self.insert_timer_ref(e);
                    self.primary.insert(absolute_bytes[3], weak_e, []);
                    Ok(())
                }
                [0, 0, _, _] => {
                    let weak_e = self.insert_timer_ref(e);
                    self.secondary
                        .insert(absolute_bytes[2], weak_e, [absolute_bytes[3]]);
                    Ok(())
                }
                [0, _, _, _] => {
                    let weak_e = self.insert_timer_ref(e);
                    self.tertiary.insert(
                        absolute_bytes[1],
                        weak_e,
                        [absolute_bytes[2], absolute_bytes[3]],
                    );
                    Ok(())
                }
                [_, _, _, _] => {
                    let weak_e = self.insert_timer_ref(e);
                    self.quarternary.insert(
                        absolute_bytes[0],
                        weak_e,
                        [absolute_bytes[1], absolute_bytes[2], absolute_bytes[3]],
                    );
                    Ok(())
                }
            }
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

    fn is_alive(&self, weak_e: &Weak<EntryType>) -> bool {
        match weak_e.upgrade() {
            Some(_) => true,
            None => false,
        }
    }

    /// Move the wheel forward by a single unit (ms)
    ///
    /// Returns a list of all timers that expire during this tick.
    pub fn tick(&mut self) -> Vec<Rc<EntryType>> {
        let mut res: Vec<Rc<EntryType>> = Vec::new();
        // primary
        let mut move0: WheelEntryList<EntryType, [u8; 0]> = Vec::new();
        let current0 = self.primary.tick(&mut move0);
        for we in move0.drain(..) {
            if let Some(e) = self.take_timer(we.entry) {
                res.push(e);
            }
        }
        if current0 == 0u8 {
            // secondary
            let mut move1: WheelEntryList<EntryType, [u8; 1]> = Vec::new();
            let current1 = self.secondary.tick(&mut move1);
            for we in move1.drain(..) {
                if we.rest[0] == 0u8 {
                    if let Some(e) = self.take_timer(we.entry) {
                        res.push(e);
                    }
                } else {
                    if self.is_alive(&we.entry) {
                        self.primary.insert(we.rest[0], we.entry, []);
                    }
                }
            }
            if current1 == 0u8 {
                // tertiary
                let mut move2: WheelEntryList<EntryType, [u8; 2]> = Vec::new();
                let current2 = self.tertiary.tick(&mut move2);
                for we in move2.drain(..) {
                    match we.rest {
                        [0, 0] => {
                            if let Some(e) = self.take_timer(we.entry) {
                                res.push(e)
                            }
                        }
                        [0, b0] => {
                            if self.is_alive(&we.entry) {
                                self.primary.insert(b0, we.entry, []);
                            }
                        }
                        [b1, b0] => {
                            if self.is_alive(&we.entry) {
                                self.secondary.insert(b1, we.entry, [b0]);
                            }
                        }
                    }
                }
                if current2 == 0u8 {
                    // quaternary
                    let mut move3: WheelEntryList<EntryType, [u8; 3]> = Vec::new();
                    let current3 = self.quarternary.tick(&mut move3);
                    for we in move3.drain(..) {
                        match we.rest {
                            [0, 0, 0] => {
                                if let Some(e) = self.take_timer(we.entry) {
                                    res.push(e)
                                }
                            }
                            [0, 0, b0] => {
                                if self.is_alive(&we.entry) {
                                    self.primary.insert(b0, we.entry, []);
                                }
                            }
                            [0, b1, b0] => {
                                if self.is_alive(&we.entry) {
                                    self.secondary.insert(b1, we.entry, [b0]);
                                }
                            }
                            [b2, b1, b0] => {
                                if self.is_alive(&we.entry) {
                                    self.tertiary.insert(b2, we.entry, [b1, b0]);
                                }
                            }
                        }
                    }
                    if current3 == 0u8 {
                        // overflow list
                        if !self.overflow.is_empty() {
                            let mut ol = Vec::with_capacity(self.overflow.len() / 2); // assume that about half are going to be scheduled now
                            mem::swap(&mut self.overflow, &mut ol);
                            for overflow_e in ol.drain(..) {
                                if let Some(rc_e) = self.take_timer(overflow_e.entry) {
                                    match self
                                        .insert_ref_with_delay(rc_e, overflow_e.remaining_delay)
                                    {
                                        Ok(()) => (), // ignore
                                        Err(TimerError::Expired(e)) => res.push(e),
                                        Err(f) => panic!("Unexpected error during insert: {:?}", f),
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        res
    }

    /// Skip a certain `amount` of units (ms)
    ///
    /// No timers will be executed for the skipped time.
    /// Only use this after determining that it's actually
    /// valid with [can_skip](QuadWheelWithOverflow::can_skip)!
    pub fn skip(&mut self, amount: u32) {
        let new_time = self.current_time_in_cycle().wrapping_add(amount);
        let new_time_bytes: [u8; 4] = unsafe { mem::transmute(new_time.to_be()) };
        self.primary.current = new_time_bytes[3];
        self.secondary.current = new_time_bytes[2];
        self.tertiary.current = new_time_bytes[1];
        self.quarternary.current = new_time_bytes[0];
    }

    /// Determine if and how many ticks can be skipped
    pub fn can_skip(&self) -> Skip {
        if self.primary.is_empty() {
            if self.secondary.is_empty() {
                if self.tertiary.is_empty() {
                    if self.quarternary.is_empty() {
                        if self.overflow.is_empty() {
                            Skip::Empty
                        } else {
                            Skip::from_millis((self.remaining_time_in_cycle() - 1u64) as u32)
                        }
                    } else {
                        let tertiary_current =
                            self.current_time_in_cycle() & (TERTIARY_LENGTH - 1u32); // just zero highest byte
                        let rem = TERTIARY_LENGTH - tertiary_current;
                        Skip::from_millis(rem - 1u32)
                    }
                } else {
                    let secondary_current =
                        self.current_time_in_cycle() & (SECONDARY_LENGTH - 1u32); // zero highest 2 bytes
                    let rem = SECONDARY_LENGTH - secondary_current;
                    Skip::from_millis(rem - 1u32)
                }
            } else {
                let primary_current = self.primary.current as u32;
                let rem = PRIMARY_LENGTH - primary_current;
                Skip::from_millis(rem - 1u32)
            }
        } else {
            Skip::None
        }
    }
}

/// Result of a [can_skip](QuadWheelWithOverflow::can_skip) invocation
#[derive(PartialEq, Debug)]
pub enum Skip {
    /// The wheel is completely empty, so there's no point in skipping
    ///
    /// In fact, this may be a good opportunity to reset the wheel, if the
    /// time semantics allow for that.
    Empty,
    /// It's possible to skip up to the provided number of ticks (in ms)
    Millis(u32),
    /// Nothing can be skipped, as the next tick has expiring timers
    None,
}

impl Skip {
    /// Provide a skip instance from ms
    ///
    /// A `ms` value of `0` will result in a `Skip::None`.
    pub fn from_millis(ms: u32) -> Skip {
        if ms == 0 {
            Skip::None
        } else {
            Skip::Millis(ms)
        }
    }

    /// A skip instance for empty wheels
    pub fn empty() -> Skip {
        Skip::Empty
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
