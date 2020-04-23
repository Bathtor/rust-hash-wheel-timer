use crate::IdOnlyTimerEntry;
use std::time::Duration;
use uuid::Uuid;

/// A shorthand for id timer entries that use [Uuid](uuid::Uuid) as their id type
pub type UuidOnlyTimerEntry = IdOnlyTimerEntry<Uuid>;

impl UuidOnlyTimerEntry {
    /// Produce an entry with a random [Uuid](uuid::Uuid) and the given `delay`
    ///
    /// Uses `Uuid::new_v4()` internally.
    pub fn with_random_id(delay: Duration) -> Self {
        Self::new(Uuid::new_v4(), delay)
    }
}
