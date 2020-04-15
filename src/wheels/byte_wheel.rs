use arr_macro::arr;

/// A single entry in a slot
pub struct WheelEntry<EntryType, RestType> {
    /// The actual entry
    pub entry: EntryType,
    /// The rest delay associated with the entry
    pub rest: RestType,
}

/// Just a convenience type alias for the list type used in each slot
pub type WheelEntryList<EntryType, RestType> = Vec<WheelEntry<EntryType, RestType>>;

/// A single wheel with 256 slots of for elements of `EntryType`
///
/// The `RestType` us used to store an array of bytes that are the rest of the delay.
/// This way the same wheel structure can be used at different hierarchical levels.
pub struct ByteWheel<EntryType, RestType> {
    slots: [Option<WheelEntryList<EntryType, RestType>>; 256],
    count: u64,
    current: u8,
}

impl<EntryType, RestType> ByteWheel<EntryType, RestType> {
    /// Create a new empty ByteWheel
    pub fn new() -> Self {
        let slots: [Option<WheelEntryList<EntryType, RestType>>; 256] = arr![Option::None; 256];
        ByteWheel {
            slots,
            count: 0,
            current: 0,
        }
    }

    /// Returns the index of the current slot
    pub fn current(&self) -> u8 {
        self.current
    }

    /// Advances the wheel pointer to the target index without executing anything
    ///
    /// Used for implementing "skip"-behaviours.
    pub fn advance(&mut self, to: u8) -> () {
        self.current = to;
    }

    /// Insert an entry at `pos` into the wheel and store the rest `r` with it
    pub fn insert(&mut self, pos: u8, e: EntryType, r: RestType) -> () {
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

    /// True if the number of entries is 0
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// Move the wheel by one tick and return all entries in the current slot together with the index of the next slot
    pub fn tick(&mut self) -> (Option<WheelEntryList<EntryType, RestType>>, u8) {
        self.current = self.current.wrapping_add(1u8);
        let index = self.current as usize;
        let cur = self.slots[index].take(); //mem::replace(&mut self.slots[index], None);
        if let Some(ref l) = cur {
            self.count -= l.len() as u64;
        }
        (cur, self.current)
    }
}