use std::collections::{BTreeSet, VecDeque};

use indexmap::{indexmap, IndexMap, IndexSet};

use crate::{
    automata::types::{Automaton, AutomatonSymbol, State, StateId},
    language::{Symbol, SymbolOrEpsilon, EPSILON},
    regex::RegularExpression,
};

pub trait TransitionResult {
    fn states(&self) -> impl Iterator<Item = StateId>;

    fn to_string<F: FnMut(&StateId) -> String>(&self, f: &mut F) -> String;
}

#[derive(Debug)]
pub struct FiniteAutomaton<S: AutomatonSymbol, T: TransitionResult> {
    pub states: IndexMap<StateId, State>,
    pub start_state: StateId,
    pub final_states: IndexSet<StateId>,
    pub transitions: IndexMap<StateId, IndexMap<S, T>>,
}

impl<S: AutomatonSymbol, T: TransitionResult> Automaton for FiniteAutomaton<S, T> {
    fn make_final(&mut self, state: StateId) {
        self.final_states.insert(state);
    }
}

impl<S: AutomatonSymbol, T: TransitionResult> FiniteAutomaton<S, T> {
    fn new(start_state: Option<State>) -> Self {
        let start_state = start_state.unwrap_or_default();
        let start_state_id = start_state.id();

        FiniteAutomaton {
            start_state: start_state_id,
            states: indexmap! { start_state_id => start_state },
            transitions: IndexMap::new(),
            final_states: IndexSet::new(),
        }
    }

    fn new_state(&mut self) -> StateId {
        let state = State::new();
        let id = state.id();

        self.states.insert(id, state);

        id
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
            .filter_map(|s| s.name().map(|name| (s.id(), name.to_owned())))
            .collect::<IndexMap<_, _>>();

        let mut state_idx = 1;
        let mut name_state = |id: &StateId| {
            state_names
                .entry(*id)
                .or_insert_with(|| {
                    let name = format!("q{}", state_idx);
                    state_idx += 1;
                    name
                })
                .clone()
        };

        let mut visited = IndexSet::new();
        let mut stack = vec![self.start_state];

        // Name states in order of traversal
        while let Some(state) = stack.pop() {
            if visited.insert(state) {
                name_state(&state);

                if let Some(transitions) = self.transitions.get(&state) {
                    for next_states in transitions.values() {
                        for next_state in next_states.states() {
                            stack.push(next_state);
                        }
                    }
                }
            }
        }

        for state in self.states.keys() {
            if !visited.contains(state) {
                name_state(state);
            }
        }

        let mut get_state_name = |id: &StateId| state_names.get(id).unwrap().clone();

        for (state_id, state_name) in &state_names {
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

    pub fn definition(&self) -> String {
        let mut definition = "#states\n".to_owned();

        let mut state_names = self
            .states
            .values()
            .filter_map(|s| s.name().map(|name| (s.id(), name.to_owned())))
            .collect::<IndexMap<_, _>>();

        let mut state_idx = 1;
        let mut name_state = |id: &StateId| {
            state_names
                .entry(*id)
                .or_insert_with(|| {
                    let name = format!("q{}", state_idx);
                    state_idx += 1;
                    name
                })
                .clone()
        };

        let mut visited = IndexSet::new();
        let mut stack = vec![self.start_state];

        // Name states in order of traversal
        while let Some(state) = stack.pop() {
            if visited.insert(state) {
                name_state(&state);

                if let Some(transitions) = self.transitions.get(&state) {
                    for next_states in transitions.values() {
                        for next_state in next_states.states() {
                            stack.push(next_state);
                        }
                    }
                }
            }
        }

        for state in self.states.keys() {
            if !visited.contains(state) {
                name_state(state);
            }
        }

        for state_name in state_names.values() {
            definition.push_str(&format!("{}\n", state_name));
        }

        definition.push_str(&format!("#initial\n{}\n", state_names[&self.start_state]));
        definition.push_str("#accepting\n");
        for state_id in &self.final_states {
            definition.push_str(&format!("{}\n", state_names[state_id]));
        }

        let symbols = self
            .transitions
            .values()
            .flat_map(|map| map.keys().map(|s| (s.as_str(), s)))
            .collect::<IndexMap<_, _>>();

        definition.push_str("#alphabet\n");
        for symbol in symbols.keys() {
            definition.push_str(&format!("{}\n", symbol));
        }

        definition.push_str("#transitions\n");
        for (state, state_transitions) in &self.transitions {
            let state_name = state_names[state].clone();
            for (symbol, next_states) in state_transitions {
                let symbol_name = match symbol.as_str() {
                    EPSILON => "$",
                    s => s,
                };

                definition.push_str(&format!(
                    "{}:{}>{}\n",
                    state_name,
                    symbol_name,
                    next_states
                        .states()
                        .map(|next_state| state_names.get(&next_state).cloned().unwrap())
                        .collect::<Vec<_>>()
                        .join(",")
                ));
            }
        }

        definition
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

pub type EpsilonNfa = FiniteAutomaton<SymbolOrEpsilon, IndexSet<StateId>>;
pub type Nfa = FiniteAutomaton<Symbol, IndexSet<StateId>>;
pub type Dfa = FiniteAutomaton<Symbol, StateId>;

impl EpsilonNfa {
    pub fn from_definition(
        start_state: &str,
        final_states: &[&str],
        transitions: &[(&str, &str, &[&str])],
    ) -> EpsilonNfa {
        let mut state_map = IndexMap::new();

        let mut epsilon_nfa = EpsilonNfa::new(Some(State::with_name(start_state)));
        state_map.insert(start_state.to_string(), epsilon_nfa.start_state);

        for &final_state in final_states {
            let state = state_map.entry(final_state.to_string()).or_insert_with(|| {
                let state = State::with_name(final_state);
                let id = state.id();
                epsilon_nfa.states.insert(id, state);
                id
            });

            epsilon_nfa.make_final(*state);
        }

        for (from, symbol, to) in transitions.iter().copied() {
            let from_state = *state_map.entry(from.to_string()).or_insert_with(|| {
                let state = State::with_name(from);
                let id = state.id();
                epsilon_nfa.states.insert(id, state);
                id
            });

            let symbol = match symbol {
                EPSILON => SymbolOrEpsilon::Epsilon,
                s => SymbolOrEpsilon::Symbol(Symbol::new(s.to_string())),
            };

            for to_state in to.iter().copied() {
                let to_state = *state_map.entry(to_state.to_string()).or_insert_with(|| {
                    let state = State::with_name(to_state);
                    let id = state.id();
                    epsilon_nfa.states.insert(id, state);
                    id
                });

                epsilon_nfa.link(from_state, symbol.clone(), to_state);
            }
        }

        epsilon_nfa
    }

    fn link(&mut self, from: StateId, symbol: SymbolOrEpsilon, to: StateId) {
        self.transitions
            .entry(from)
            .or_insert_with(IndexMap::new)
            .entry(symbol)
            .or_insert_with(IndexSet::new)
            .insert(to);
    }

    fn merge_states(&mut self, dest: StateId, src: StateId) {
        if self.start_state == src {
            self.start_state = dest;
        }

        if self.final_states.shift_remove(&src) {
            self.final_states.insert(dest);
        }

        for state_transitions in self.transitions.values_mut() {
            for next_states in state_transitions.values_mut() {
                if next_states.shift_remove(&src) {
                    next_states.insert(dest);
                }
            }
        }

        if let Some(src_transitions) = self.transitions.shift_remove(&src) {
            for (src_symbol, src_next_states) in src_transitions {
                let dest_transitions = self.transitions.entry(dest).or_insert_with(IndexMap::new);

                dest_transitions
                    .entry(src_symbol)
                    .or_insert_with(IndexSet::new)
                    .extend(src_next_states);
            }
        }

        self.states.shift_remove(&src);
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
                if *symbol == SymbolOrEpsilon::Epsilon {
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
    pub fn from_definition(
        start_state: &str,
        final_states: &[&str],
        transitions: &[(&str, &str, &[&str])],
    ) -> Nfa {
        let mut state_map = IndexMap::new();

        let mut nfa = Nfa::new(Some(State::with_name(start_state)));
        state_map.insert(start_state.to_string(), nfa.start_state);

        for &final_state in final_states {
            let state = state_map.entry(final_state.to_string()).or_insert_with(|| {
                let state = State::with_name(final_state);
                let id = state.id();
                nfa.states.insert(id, state);
                id
            });

            nfa.make_final(*state);
        }

        for (from, symbol, to) in transitions.iter().copied() {
            let from_state = *state_map.entry(from.to_string()).or_insert_with(|| {
                let state = State::with_name(from);
                let id = state.id();
                nfa.states.insert(id, state);
                id
            });

            let symbol = Symbol::new(symbol.to_string());

            for to_state in to.iter().copied() {
                let to_state = *state_map.entry(to_state.to_string()).or_insert_with(|| {
                    let state = State::with_name(to_state);
                    let id = state.id();
                    nfa.states.insert(id, state);
                    id
                });

                nfa.link(from_state, symbol.clone(), to_state);
            }
        }

        nfa
    }

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

impl Dfa {
    pub fn from_definition(
        start_state: &str,
        final_states: &[&str],
        transitions: &[(&str, &str, &str)],
    ) -> Dfa {
        let mut state_map = IndexMap::new();

        let mut dfa = Dfa::new(Some(State::with_name(start_state)));
        state_map.insert(start_state.to_string(), dfa.start_state);

        for &final_state in final_states {
            let state = state_map.entry(final_state.to_string()).or_insert_with(|| {
                let state = State::with_name(final_state);
                let id = state.id();
                dfa.states.insert(id, state);
                id
            });

            dfa.make_final(*state);
        }

        for (from, symbol, to) in transitions.iter().copied() {
            let from_state = *state_map.entry(from.to_string()).or_insert_with(|| {
                let state = State::with_name(from);
                let id = state.id();
                dfa.states.insert(id, state);
                id
            });

            let symbol = Symbol::new(symbol.to_string());

            let to_state = *state_map.entry(to.to_string()).or_insert_with(|| {
                let state = State::with_name(to);
                let id = state.id();
                dfa.states.insert(id, state);
                id
            });

            dfa.link(from_state, symbol.clone(), to_state);
        }

        dfa
    }

    fn link(&mut self, from: StateId, symbol: Symbol, to: StateId) {
        self.transitions
            .entry(from)
            .or_insert_with(IndexMap::new)
            .entry(symbol)
            .insert_entry(to);
    }
}

impl From<&RegularExpression> for EpsilonNfa {
    fn from(regex: &RegularExpression) -> Self {
        match regex {
            RegularExpression::Concatenation(r1, r2) => {
                let mut first_nfa = EpsilonNfa::from(r1.as_ref());
                let first_final = first_nfa.final_states[0];

                first_nfa.final_states.clear();

                let second_nfa = EpsilonNfa::from(r2.as_ref());
                let second_start = second_nfa.start_state;
                let second_final = second_nfa.final_states[0];

                first_nfa.use_finite_automaton(second_nfa);

                first_nfa.make_final(second_final);

                first_nfa.merge_states(first_final, second_start);

                first_nfa
            }
            regex => {
                let mut epsilon_nfa = EpsilonNfa::new(None);

                let start_state = epsilon_nfa.start_state;
                let final_state = epsilon_nfa.new_state();
                epsilon_nfa.make_final(final_state);

                match regex {
                    RegularExpression::Zero => {}
                    RegularExpression::One => {
                        epsilon_nfa.link(start_state, SymbolOrEpsilon::Epsilon, final_state);
                    }
                    RegularExpression::Symbol(s) => {
                        epsilon_nfa.link(
                            start_state,
                            SymbolOrEpsilon::Symbol(s.clone()),
                            final_state,
                        );
                    }
                    RegularExpression::Union(r1, r2) => {
                        let first_nfa = EpsilonNfa::from(r1.as_ref());
                        let first_start = first_nfa.start_state;
                        let first_final = first_nfa.final_states[0];

                        epsilon_nfa.use_finite_automaton(first_nfa);

                        let second_nfa = EpsilonNfa::from(r2.as_ref());
                        let second_start = second_nfa.start_state;
                        let second_final = second_nfa.final_states[0];

                        epsilon_nfa.use_finite_automaton(second_nfa);

                        epsilon_nfa.link(start_state, SymbolOrEpsilon::Epsilon, first_start);
                        epsilon_nfa.link(start_state, SymbolOrEpsilon::Epsilon, second_start);

                        epsilon_nfa.link(first_final, SymbolOrEpsilon::Epsilon, final_state);
                        epsilon_nfa.link(second_final, SymbolOrEpsilon::Epsilon, final_state);
                    }
                    RegularExpression::KleeneStar(r) => {
                        let inner_nfa = EpsilonNfa::from(r.as_ref());
                        let inner_start = inner_nfa.start_state;
                        let inner_final = inner_nfa.final_states[0];

                        epsilon_nfa.use_finite_automaton(inner_nfa);

                        epsilon_nfa.link(start_state, SymbolOrEpsilon::Epsilon, inner_start);
                        epsilon_nfa.link(inner_final, SymbolOrEpsilon::Epsilon, final_state);

                        epsilon_nfa.link(inner_final, SymbolOrEpsilon::Epsilon, inner_start);
                        epsilon_nfa.link(start_state, SymbolOrEpsilon::Epsilon, final_state);
                    }
                    RegularExpression::Plus(r) => {
                        let inner_nfa = EpsilonNfa::from(r.as_ref());
                        let inner_start = inner_nfa.start_state;
                        let inner_final = inner_nfa.final_states[0];

                        epsilon_nfa.use_finite_automaton(inner_nfa);

                        epsilon_nfa.link(start_state, SymbolOrEpsilon::Epsilon, inner_start);
                        epsilon_nfa.link(inner_final, SymbolOrEpsilon::Epsilon, final_state);

                        epsilon_nfa.link(inner_final, SymbolOrEpsilon::Epsilon, inner_start);
                    }
                    _ => unreachable!(),
                }

                epsilon_nfa
            }
        }
    }
}

impl From<&EpsilonNfa> for Nfa {
    fn from(epsilon_nfa: &EpsilonNfa) -> Self {
        let mut nfa = Nfa::new(Some(epsilon_nfa.states[&epsilon_nfa.start_state].clone()));

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
                            SymbolOrEpsilon::Symbol(symbol) => {
                                for next_state in next_states {
                                    nfa.link(state, symbol.clone(), *next_state);
                                }
                            }
                            SymbolOrEpsilon::Epsilon => {
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

impl From<&Nfa> for Dfa {
    fn from(nfa: &Nfa) -> Self {
        let start_state_set = BTreeSet::from([nfa.start_state]);

        let mut dfa = Dfa::new(None);

        let mut state_map = IndexMap::from([(start_state_set.clone(), dfa.start_state)]);

        let mut queue = VecDeque::from([start_state_set]);

        let symbols = nfa
            .transitions
            .values()
            .flat_map(|map| map.keys())
            .collect::<IndexSet<_>>();

        while let Some(current_set) = queue.pop_front() {
            let dfa_state = state_map.get(&current_set).cloned().unwrap();
            for state in &current_set {
                if nfa.final_states.contains(state) {
                    dfa.make_final(dfa_state);
                }
            }

            for symbol in symbols.iter().copied() {
                let mut next_set = BTreeSet::new();

                for state in current_set.iter() {
                    if let Some(transitions) = nfa.transitions.get(state) {
                        if let Some(next_states) = transitions.get(symbol) {
                            next_set.extend(next_states.states());
                        }
                    }
                }

                let next_state = state_map
                    .entry(next_set.clone())
                    .or_insert_with(|| {
                        queue.push_back(next_set.clone());
                        dfa.new_state()
                    })
                    .clone();

                dfa.link(dfa_state, symbol.clone(), next_state);
            }
        }

        dfa
    }
}
