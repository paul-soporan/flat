use uuid::Uuid;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StateId(Uuid);

#[derive(Debug, Clone)]
pub struct State {
    pub id: StateId,
    pub name: Option<String>,
}

impl State {
    pub fn new(name: Option<String>) -> Self {
        State {
            id: StateId(Uuid::new_v4()),
            name,
        }
    }
}
