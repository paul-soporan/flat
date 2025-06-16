use std::fmt::Display;

use derive_more::Display;
use indexmap::{indexmap, IndexMap, IndexSet};
use itertools::Itertools;

use crate::{
    automata::types::{State, StateId},
    language::{Symbol, SymbolOrEpsilon, Word, EPSILON},
};

#[derive(Debug, Display, Clone, PartialEq, Eq, Hash)]
struct TapeSymbol(SymbolOrEpsilon);

#[derive(Debug, Display, Clone, PartialEq, Eq, Hash)]
struct StackSymbol(SymbolOrEpsilon);

#[derive(Debug)]
struct InstantaneousDescription<'a> {
    pushdown_automaton: &'a PushdownAutomaton,
    tape: Vec<Symbol>,
    tape_index: usize,
    stack: Vec<Symbol>,
    state: StateId,
}

impl<'a> InstantaneousDescription<'a> {
    fn initial(
        pushdown_automaton: &'a PushdownAutomaton,
        tape_symbols: impl IntoIterator<Item = Symbol>,
    ) -> Self {
        Self {
            pushdown_automaton,
            tape: Vec::from_iter(tape_symbols),
            tape_index: 0,
            stack: vec![pushdown_automaton.initial_stack_symbol.clone()],
            state: pushdown_automaton.start_state,
        }
    }

    fn is_accepting(&self) -> bool {
        self.tape_index == self.tape.len()
            && (self.stack.is_empty() || self.pushdown_automaton.final_states.contains(&self.state))
    }

    fn use_transition(
        &mut self,
        &(new_state, pushed_stack_symbols, is_epsilon_transition): &(
            &StateId,
            &Vec<StackSymbol>,
            bool,
        ),
    ) {
        self.state = *new_state;
        if !is_epsilon_transition {
            self.tape_index += 1;
        }

        for symbol in pushed_stack_symbols.iter().rev() {
            match symbol {
                StackSymbol(SymbolOrEpsilon::Epsilon) => continue,
                StackSymbol(SymbolOrEpsilon::Symbol(s)) => self.stack.push(s.clone()),
            }
        }
    }

    fn run(&mut self) -> bool {
        println!("{}", self);

        if self.is_accepting() {
            return true;
        }

        let current_stack_symbol = match self.stack.pop() {
            Some(symbol) => symbol,
            None => return false,
        };
        let current_tape_symbol = if self.tape_index < self.tape.len() {
            Some(self.tape[self.tape_index].clone())
        } else {
            None
        };

        let state_transitions = match self.pushdown_automaton.transitions.get(&self.state) {
            Some(transitions) => transitions,
            None => return false,
        };

        let tape_transitions = current_tape_symbol
            .map(|current_tape_symbol| {
                state_transitions.get(&(
                    TapeSymbol(SymbolOrEpsilon::Symbol(current_tape_symbol)),
                    StackSymbol(SymbolOrEpsilon::Symbol(current_stack_symbol.clone())),
                ))
            })
            .flatten();

        let epsilon_transitions = state_transitions.get(&(
            TapeSymbol(SymbolOrEpsilon::Epsilon),
            StackSymbol(SymbolOrEpsilon::Symbol(current_stack_symbol)),
        ));

        let transitions = tape_transitions
            .into_iter()
            .flat_map(|transitions| {
                transitions
                    .iter()
                    .map(|(state, symbols)| (state, symbols, false))
            })
            .chain(epsilon_transitions.into_iter().flat_map(|transitions| {
                transitions
                    .iter()
                    .map(|(state, symbols)| (state, symbols, true))
            }))
            .collect::<Vec<_>>();

        if transitions.is_empty() {
            return false;
        }

        let transition_count = transitions.len();

        let mut transitions = transitions.into_iter();
        let first_transition = transitions.next().unwrap();

        if transition_count > 1 {
            let old_state = self.state;
            let old_tape_index = self.tape_index;
            let old_stack = self.stack.clone();

            for transition in transitions {
                self.use_transition(&transition);

                if self.run() {
                    return true;
                }

                self.state = old_state;
                self.tape_index = old_tape_index;
                self.stack = old_stack.clone();
            }
        }

        self.use_transition(&first_transition);

        return self.run();
    }
}

impl Display for InstantaneousDescription<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let current_state = self.pushdown_automaton.states.get(&self.state).unwrap();

        write!(
            f,
            "({}, {}, {})",
            current_state.name().unwrap_or_else(|| "q?"),
            if self.tape[self.tape_index..].is_empty() {
                EPSILON.to_string()
            } else {
                self.tape.iter().skip(self.tape_index).join("")
            },
            if self.stack.is_empty() {
                EPSILON.to_string()
            } else {
                self.stack.iter().join("")
            }
        )
    }
}

#[derive(Debug)]
pub struct PushdownAutomaton {
    states: IndexMap<StateId, State>,
    start_state: StateId,
    final_states: IndexSet<StateId>,
    initial_stack_symbol: Symbol,
    transitions:
        IndexMap<StateId, IndexMap<(TapeSymbol, StackSymbol), Vec<(StateId, Vec<StackSymbol>)>>>,
}

impl PushdownAutomaton {
    pub fn new(start_state: Option<State>, initial_stack_symbol: Symbol) -> Self {
        let start_state = start_state.unwrap_or_default();
        let start_state_id = start_state.id();

        Self {
            initial_stack_symbol,
            start_state: start_state_id,
            states: indexmap! { start_state_id => start_state },
            final_states: IndexSet::new(),
            transitions: IndexMap::new(),
        }
    }

    pub fn from_definition(
        start_state: &str,
        initial_stack_symbol: &str,
        final_states: &[&str],
        transitions: &[(&str, &str, &str, &[(&[&str], &str)])],
    ) -> Self {
        let mut state_map = IndexMap::new();

        let mut pda = Self::new(
            Some(State::with_name(start_state)),
            Symbol::new(initial_stack_symbol),
        );
        state_map.insert(start_state.to_string(), pda.start_state);

        for &final_state in final_states {
            let state = state_map.entry(final_state.to_string()).or_insert_with(|| {
                let state = State::with_name(final_state);
                let id = state.id();
                pda.states.insert(id, state);
                id
            });

            pda.make_final(*state);
        }

        for (from, tape_symbol, popped_stack_symbol, to) in transitions.iter().copied() {
            let from_state = *state_map.entry(from.to_string()).or_insert_with(|| {
                let state = State::with_name(from);
                let id = state.id();
                pda.states.insert(id, state);
                id
            });

            let tape_symbol = TapeSymbol(match tape_symbol {
                EPSILON => SymbolOrEpsilon::Epsilon,
                s => SymbolOrEpsilon::Symbol(Symbol::new(s.to_string())),
            });

            let popped_stack_symbol = StackSymbol(match popped_stack_symbol {
                EPSILON => SymbolOrEpsilon::Epsilon,
                s => SymbolOrEpsilon::Symbol(Symbol::new(s)),
            });

            for (pushed_stack_symbols, to_state) in to.iter().copied() {
                let to_state = *state_map.entry(to_state.to_string()).or_insert_with(|| {
                    let state = State::with_name(to_state);
                    let id = state.id();
                    pda.states.insert(id, state);
                    id
                });

                let pushed_stack_symbols = pushed_stack_symbols
                    .iter()
                    .map(|s| {
                        StackSymbol(match *s {
                            EPSILON => SymbolOrEpsilon::Epsilon,
                            s => SymbolOrEpsilon::Symbol(Symbol::new(s.to_string())),
                        })
                    })
                    .collect();

                pda.link(
                    from_state,
                    tape_symbol.clone(),
                    popped_stack_symbol.clone(),
                    pushed_stack_symbols,
                    to_state,
                );
            }
        }

        pda
    }

    fn make_final(&mut self, state: StateId) {
        self.final_states.insert(state);
    }

    fn link(
        &mut self,
        from: StateId,
        tape_symbol: TapeSymbol,
        popped_stack_symbol: StackSymbol,
        pushed_stack_symbols: Vec<StackSymbol>,
        to: StateId,
    ) {
        self.transitions
            .entry(from)
            .or_insert_with(IndexMap::new)
            .entry((tape_symbol, popped_stack_symbol))
            .or_insert_with(Vec::new)
            .push((to, pushed_stack_symbols));
    }

    pub fn run(&self, input: &Word<Symbol>) -> bool {
        let mut id = InstantaneousDescription::initial(self, input.clone());

        id.run()
    }
}
