use crate::wheels::{CancellableTimerEntry, TimerEntryWithDelay};
use std::time::Duration;
use uuid::Uuid;

#[derive(Debug)]
pub struct IdOnlyTimerEntry {
    pub id: Uuid,
    pub delay: Duration,
}
impl IdOnlyTimerEntry {
    pub fn new(id: Uuid, delay: Duration) -> Self {
        IdOnlyTimerEntry { id, delay }
    }

    pub fn with_random_id(delay: Duration) -> Self {
        Self::new(Uuid::new_v4(), delay)
    }
}
impl CancellableTimerEntry for IdOnlyTimerEntry {
    type Id = Uuid;

    fn id(&self) -> &Self::Id {
        &self.id
    }
}

impl TimerEntryWithDelay for IdOnlyTimerEntry {
    fn delay(&self) -> Duration {
        self.delay
    }
}
