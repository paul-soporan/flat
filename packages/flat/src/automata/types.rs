use std::hash::Hash;

use uuid::Uuid;

use crate::language::{Symbol, SymbolOrEpsilon, EPSILON};

// TODO: Why derive Ord?
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StateId(Uuid);

#[derive(Debug, Clone)]
pub struct State {
    id: StateId,
    name: Option<String>,
}

impl State {
    pub fn new() -> Self {
        Self {
            id: StateId(Uuid::new_v4()),
            name: None,
        }
    }

    pub fn with_name(name: impl Into<String>) -> Self {
        Self {
            id: StateId(Uuid::new_v4()),
            name: Some(name.into()),
        }
    }

    pub fn id(&self) -> StateId {
        self.id
    }

    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }
}

impl Default for State {
    fn default() -> Self {
        Self::new()
    }
}

pub trait AutomatonSymbol: Eq + Hash {
    fn as_str(&self) -> &str;
}

impl AutomatonSymbol for Symbol {
    fn as_str(&self) -> &str {
        self.as_str()
    }
}

impl AutomatonSymbol for SymbolOrEpsilon {
    fn as_str(&self) -> &str {
        match self {
            SymbolOrEpsilon::Epsilon => EPSILON,
            SymbolOrEpsilon::Symbol(s) => s.as_str(),
        }
    }
}
