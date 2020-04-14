use crate::IdOnlyTimerEntry;
use std::time::Duration;
use uuid::Uuid;

pub type UuidOnlyTimerEntry = IdOnlyTimerEntry<Uuid>;

impl UuidOnlyTimerEntry {
    pub fn with_random_id(delay: Duration) -> Self {
        Self::new(Uuid::new_v4(), delay)
    }
}
