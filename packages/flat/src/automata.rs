use std::hash::Hash;

use indexmap::{indexmap, IndexMap, IndexSet};
use uuid::Uuid;

use crate::{language::Symbol, regex::RegularExpression};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StateId(Uuid);

#[derive(Debug, Clone)]
pub struct State {
    id: StateId,
    name: Option<String>,
}

impl State {
    pub fn new(name: Option<String>) -> Self {
        State {
            id: StateId(Uuid::new_v4()),
            name,
        }
    }
}

pub trait FiniteAutomatonSymbol: Hash + Eq {
    fn as_str(&self) -> &str;
}

pub trait TransitionResult {
    fn states(&self) -> impl Iterator<Item = StateId>;

    fn to_string<F: FnMut(&StateId) -> String>(&self, f: &mut F) -> String;
}

#[derive(Debug)]
pub struct FiniteAutomaton<S: FiniteAutomatonSymbol, T: TransitionResult> {
    states: IndexMap<StateId, State>,
    // pub alphabet: Vec<Symbol>,
    transitions: IndexMap<StateId, IndexMap<S, T>>,
    start_state: StateId,
    final_states: IndexSet<StateId>,
}

impl<S: FiniteAutomatonSymbol, T: TransitionResult> FiniteAutomaton<S, T> {
    fn new() -> Self {
        let start_state = State::new(None);

        FiniteAutomaton {
            start_state: start_state.id,
            states: indexmap! { start_state.id => start_state },
            transitions: IndexMap::new(),
            final_states: IndexSet::new(),
        }
    }

    fn new_with_start_state(start_state: State) -> Self {
        FiniteAutomaton {
            start_state: start_state.id,
            states: indexmap! { start_state.id => start_state },
            transitions: IndexMap::new(),
            final_states: IndexSet::new(),
        }
    }

    fn new_state(&mut self) -> StateId {
        let state = State::new(None);
        let id = state.id;

        self.states.insert(id, state);

        id
    }

    fn make_final(&mut self, state: StateId) {
        self.final_states.insert(state);
    }

    fn use_finite_automaton(&mut self, other: Self) {
        self.states.extend(other.states);
        self.transitions.extend(other.transitions);
    }

    pub fn transition_table(&self) -> String {
        let mut symbols = self
            .transitions
            .values()
            .flat_map(|map| map.keys().map(|s| (s.as_str(), s)))
            .collect::<IndexMap<_, _>>();

        symbols.sort_keys();

        let mut table = "|δ|".to_string();
        for symbol in symbols.keys() {
            table.push_str(&format!("{}|", symbol));
        }
        table.push_str("\n");

        table.push_str("|:---:|");
        for _ in symbols.keys() {
            table.push_str(":---:|");
        }
        table.push_str("\n");

        let mut state_names = self
            .states
            .values()
            .filter_map(|s| s.name.clone().map(|name| (s.id, name)))
            .collect::<IndexMap<_, _>>();

        let mut state_idx = 0;
        let mut get_state_name = |id: &StateId| {
            state_names
                .entry(*id)
                .or_insert_with(|| {
                    let name = format!("q{}", state_idx);
                    state_idx += 1;
                    name
                })
                .clone()
        };

        for state_id in self.states.keys() {
            let state_name = get_state_name(state_id);
            let state_transitions = self.transitions.get(state_id);

            table.push_str(&format!("|{}|", {
                let prefix = if state_id == &self.start_state {
                    "→"
                } else {
                    ""
                };
                let suffix = if self.final_states.contains(state_id) {
                    "*"
                } else {
                    ""
                };

                format!("{}{}{}", prefix, state_name, suffix)
            }));
            for &symbol in symbols.values() {
                if let Some(transition) =
                    state_transitions.and_then(|transitions| transitions.get(symbol))
                {
                    table.push_str(&format!("{}|", transition.to_string(&mut get_state_name)));
                } else {
                    table.push_str("|");
                }
            }
            table.push_str("\n");
        }

        table
    }
}

impl FiniteAutomatonSymbol for Symbol {
    fn as_str(&self) -> &str {
        self.as_str()
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum EpsilonNfaSymbol {
    Epsilon,
    Symbol(Symbol),
}

impl FiniteAutomatonSymbol for EpsilonNfaSymbol {
    fn as_str(&self) -> &str {
        match self {
            EpsilonNfaSymbol::Epsilon => "ε",
            EpsilonNfaSymbol::Symbol(s) => s.as_str(),
        }
    }
}

impl TransitionResult for IndexSet<StateId> {
    fn states(&self) -> impl Iterator<Item = StateId> {
        self.iter().copied()
    }

    fn to_string<F: FnMut(&StateId) -> String>(&self, f: &mut F) -> String {
        format!("{{{}}}", self.iter().map(f).collect::<Vec<_>>().join(", "))
    }
}
impl TransitionResult for StateId {
    fn states(&self) -> impl Iterator<Item = StateId> {
        std::iter::once(*self)
    }

    fn to_string<F: FnMut(&StateId) -> String>(&self, f: &mut F) -> String {
        f(self)
    }
}

pub type EpsilonNfa = FiniteAutomaton<EpsilonNfaSymbol, IndexSet<StateId>>;
pub type Nfa = FiniteAutomaton<Symbol, IndexSet<StateId>>;
pub type Dfa = FiniteAutomaton<Symbol, StateId>;

impl EpsilonNfa {
    fn link(&mut self, from: StateId, symbol: EpsilonNfaSymbol, to: StateId) {
        self.transitions
            .entry(from)
            .or_insert_with(IndexMap::new)
            .entry(symbol)
            .or_insert_with(IndexSet::new)
            .insert(to);
    }

    fn epsilon_closure(
        &self,
        state: &StateId,
        visited: &mut IndexSet<StateId>,
    ) -> IndexSet<StateId> {
        if visited.contains(state) {
            return visited.clone();
        }

        visited.insert(*state);

        if let Some(transitions) = self.transitions.get(state) {
            for (symbol, next_states) in transitions {
                if *symbol == EpsilonNfaSymbol::Epsilon {
                    for next_state in next_states {
                        self.epsilon_closure(next_state, visited);
                    }
                }
            }
        }

        visited.clone()
    }
}

impl Nfa {
    fn link(&mut self, from: StateId, symbol: Symbol, to: StateId) {
        self.transitions
            .entry(from)
            .or_insert_with(IndexMap::new)
            .entry(symbol)
            .or_insert_with(IndexSet::new)
            .insert(to);
    }

    pub fn remove_unreachable_states(&mut self) {
        let mut reachable_states = IndexSet::new();
        let mut stack = vec![self.start_state];

        while let Some(state) = stack.pop() {
            if reachable_states.insert(state) {
                if let Some(transitions) = self.transitions.get(&state) {
                    for next_states in transitions.values() {
                        for next_state in next_states.states() {
                            stack.push(next_state);
                        }
                    }
                }
            }
        }

        self.states.retain(|id, _| reachable_states.contains(id));
        self.final_states.retain(|id| reachable_states.contains(id));

        self.transitions = self
            .transitions
            .clone()
            .into_iter()
            .filter_map(|(state, state_transitions)| {
                if !reachable_states.contains(&state) {
                    return None;
                }

                let filtered_transitions = state_transitions
                    .into_iter()
                    .filter_map(|(symbol, next_states)| {
                        let filtered_states = next_states
                            .states()
                            .filter(|next_state| reachable_states.contains(next_state))
                            .collect::<IndexSet<_>>();

                        if filtered_states.is_empty() {
                            None
                        } else {
                            Some((symbol, filtered_states))
                        }
                    })
                    .collect::<IndexMap<_, _>>();

                if filtered_transitions.is_empty() {
                    None
                } else {
                    Some((state, filtered_transitions))
                }
            })
            .collect::<IndexMap<_, _>>();
    }
}

impl From<RegularExpression> for EpsilonNfa {
    fn from(regex: RegularExpression) -> Self {
        match regex {
            RegularExpression::Concatenation(r1, r2) => {
                let mut first_nfa = EpsilonNfa::from(*r1);
                let first_final = first_nfa.final_states[0];

                first_nfa.final_states.clear();

                let second_nfa = EpsilonNfa::from(*r2);
                let second_start = second_nfa.start_state;
                let second_final = second_nfa.final_states[0];

                first_nfa.use_finite_automaton(second_nfa);

                first_nfa.make_final(second_final);

                // TODO: Merge these 2 states.
                first_nfa.link(first_final, EpsilonNfaSymbol::Epsilon, second_start);

                first_nfa
            }
            regex => {
                let mut epsilon_nfa = EpsilonNfa::new();

                let start_state = epsilon_nfa.start_state;
                let final_state = epsilon_nfa.new_state();
                epsilon_nfa.make_final(final_state);

                match regex {
                    RegularExpression::Zero => {}
                    RegularExpression::One => {
                        epsilon_nfa.link(start_state, EpsilonNfaSymbol::Epsilon, final_state);
                    }
                    RegularExpression::Symbol(s) => {
                        epsilon_nfa.link(start_state, EpsilonNfaSymbol::Symbol(s), final_state);
                    }
                    RegularExpression::Union(r1, r2) => {
                        let first_nfa = EpsilonNfa::from(*r1);
                        let first_start = first_nfa.start_state;
                        let first_final = first_nfa.final_states[0];

                        epsilon_nfa.use_finite_automaton(first_nfa);

                        let second_nfa = EpsilonNfa::from(*r2);
                        let second_start = second_nfa.start_state;
                        let second_final = second_nfa.final_states[0];

                        epsilon_nfa.use_finite_automaton(second_nfa);

                        epsilon_nfa.link(start_state, EpsilonNfaSymbol::Epsilon, first_start);
                        epsilon_nfa.link(start_state, EpsilonNfaSymbol::Epsilon, second_start);

                        epsilon_nfa.link(first_final, EpsilonNfaSymbol::Epsilon, final_state);
                        epsilon_nfa.link(second_final, EpsilonNfaSymbol::Epsilon, final_state);
                    }
                    RegularExpression::KleeneStar(r) => {
                        let inner_nfa = EpsilonNfa::from(*r);
                        let inner_start = inner_nfa.start_state;
                        let inner_final = inner_nfa.final_states[0];

                        epsilon_nfa.use_finite_automaton(inner_nfa);

                        epsilon_nfa.link(start_state, EpsilonNfaSymbol::Epsilon, inner_start);
                        epsilon_nfa.link(inner_final, EpsilonNfaSymbol::Epsilon, final_state);

                        epsilon_nfa.link(inner_final, EpsilonNfaSymbol::Epsilon, inner_start);
                        epsilon_nfa.link(start_state, EpsilonNfaSymbol::Epsilon, final_state);
                    }
                    RegularExpression::Plus(r) => {
                        let inner_nfa = EpsilonNfa::from(*r);
                        let inner_start = inner_nfa.start_state;
                        let inner_final = inner_nfa.final_states[0];

                        epsilon_nfa.use_finite_automaton(inner_nfa);

                        epsilon_nfa.link(start_state, EpsilonNfaSymbol::Epsilon, inner_start);
                        epsilon_nfa.link(inner_final, EpsilonNfaSymbol::Epsilon, final_state);

                        epsilon_nfa.link(inner_final, EpsilonNfaSymbol::Epsilon, inner_start);
                    }
                    _ => unreachable!(),
                }

                epsilon_nfa
            }
        }
    }
}

impl From<EpsilonNfa> for Nfa {
    fn from(epsilon_nfa: EpsilonNfa) -> Self {
        let mut nfa =
            Nfa::new_with_start_state(epsilon_nfa.states[&epsilon_nfa.start_state].clone());

        nfa.states.extend(epsilon_nfa.states.clone());

        for &state in epsilon_nfa.states.keys() {
            let epsilon_closure = epsilon_nfa.epsilon_closure(&state, &mut IndexSet::new());
            for closure_state in epsilon_closure {
                if epsilon_nfa.final_states.contains(&closure_state) {
                    nfa.make_final(state);
                }

                let transitions = epsilon_nfa.transitions.get(&closure_state);
                if let Some(transitions) = transitions {
                    for (transition_symbol, next_states) in transitions {
                        match transition_symbol {
                            EpsilonNfaSymbol::Symbol(symbol) => {
                                for next_state in next_states {
                                    nfa.link(state, symbol.clone(), *next_state);
                                }
                            }
                            EpsilonNfaSymbol::Epsilon => {
                                // Epsilon transitions are ignored
                            }
                        }
                    }
                }
            }
        }

        nfa
    }
}
