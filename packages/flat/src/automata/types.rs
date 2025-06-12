use std::hash::Hash;

use uuid::Uuid;

// TODO: Why derive Ord?
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StateId(Uuid);

#[derive(Debug, Clone)]
pub struct State {
    id: StateId,
    name: Option<String>,
}

impl State {
    pub fn new(name: Option<String>) -> Self {
        Self {
            id: StateId(Uuid::new_v4()),
            name,
        }
    }

    pub fn id(&self) -> StateId {
        self.id
    }

    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }
}

pub trait AutomatonSymbol: Eq + Hash {
    fn as_str(&self) -> &str;
}
