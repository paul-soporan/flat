use std::fmt::Display;

use derive_more::Display;
use enumflags2::{bitflags, BitFlags};
use indexmap::{indexmap, IndexMap, IndexSet};
use itertools::Itertools;
use std::mem;

use crate::{
    automata::types::{State, StateId},
    grammars::{
        context_free::ContextFreeGrammar,
        greibach_normal_form::{GnfWord, GreibachNormalFormGrammar},
        types::{Grammar, ProductionSymbol},
    },
    language::{Symbol, SymbolOrEpsilon, Word, EPSILON},
};

#[derive(Debug, Display, Clone, PartialEq, Eq, Hash)]
struct TapeSymbol(SymbolOrEpsilon);

#[derive(Debug, Display, Clone, PartialEq, Eq, Hash)]
struct StackSymbol(SymbolOrEpsilon);

#[bitflags]
#[repr(u8)]
#[derive(Debug, Clone, Copy)]
pub enum AcceptanceCondition {
    EmptyStack = 0b01,
    FinalState = 0b10,
}

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
        if self.tape_index != self.tape.len() {
            return false;
        }

        let acceptance_condition = self.pushdown_automaton.acceptance_condition;

        if acceptance_condition.contains(AcceptanceCondition::EmptyStack) && self.stack.is_empty() {
            return true;
        }

        if acceptance_condition.contains(AcceptanceCondition::FinalState)
            && self.pushdown_automaton.final_states.contains(&self.state)
        {
            return true;
        }

        false
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
    acceptance_condition: BitFlags<AcceptanceCondition>,
}

impl PushdownAutomaton {
    pub fn new(
        start_state: Option<State>,
        initial_stack_symbol: Symbol,
        acceptance_condition: BitFlags<AcceptanceCondition>,
    ) -> Self {
        let start_state = start_state.unwrap_or_default();
        let start_state_id = start_state.id();

        Self {
            initial_stack_symbol,
            acceptance_condition,
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
        acceptance_condition: BitFlags<AcceptanceCondition>,
    ) -> Self {
        let mut state_map = IndexMap::new();

        let mut pda = Self::new(
            Some(State::with_name(start_state)),
            Symbol::new(initial_stack_symbol),
            acceptance_condition,
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

    pub fn accept_by_empty_stack(&mut self) {
        if self.acceptance_condition == AcceptanceCondition::EmptyStack {
            return;
        }

        let stack_symbols = self
            .transitions
            .values()
            .flat_map(|transitions| {
                transitions
                    .keys()
                    .map(|(_, symbol)| symbol)
                    .chain(transitions.values().flat_map(|transitions| {
                        transitions
                            .iter()
                            .flat_map(|(_, pushed_stack_symbols)| pushed_stack_symbols)
                    }))
                    .filter_map(|symbol| {
                        if let StackSymbol(SymbolOrEpsilon::Symbol(symbol)) = symbol {
                            Some(symbol.clone())
                        } else {
                            None
                        }
                    })
            })
            .collect::<IndexSet<_>>();

        let accepting_state = State::with_name("t");
        let accepting_state_id = accepting_state.id();
        self.states.insert(accepting_state_id, accepting_state);

        for state in self.final_states.clone() {
            for stack_symbol in &stack_symbols {
                self.link(
                    state,
                    TapeSymbol(SymbolOrEpsilon::Epsilon),
                    StackSymbol(SymbolOrEpsilon::Symbol(stack_symbol.clone())),
                    vec![StackSymbol(SymbolOrEpsilon::Symbol(stack_symbol.clone()))],
                    accepting_state_id,
                );
            }
        }

        for stack_symbol in &stack_symbols {
            self.link(
                accepting_state_id,
                TapeSymbol(SymbolOrEpsilon::Epsilon),
                StackSymbol(SymbolOrEpsilon::Symbol(stack_symbol.clone())),
                vec![StackSymbol(SymbolOrEpsilon::Epsilon)],
                accepting_state_id,
            );
        }

        self.final_states.clear();

        self.acceptance_condition = AcceptanceCondition::EmptyStack.into();
    }

    pub fn accept_by_final_state(&mut self) {
        if self.acceptance_condition == AcceptanceCondition::FinalState {
            return;
        }

        let old_states = self.states.clone();

        let initial_state: State = State::with_name("u");
        let initial_state_id = initial_state.id();

        let initial_stack_symbol = Symbol::new("⊥⊥");
        let old_initial_stack_symbol =
            mem::replace(&mut self.initial_stack_symbol, initial_stack_symbol.clone());

        self.link(
            initial_state_id,
            TapeSymbol(SymbolOrEpsilon::Epsilon),
            StackSymbol(SymbolOrEpsilon::Symbol(initial_stack_symbol.clone())),
            vec![
                StackSymbol(SymbolOrEpsilon::Symbol(old_initial_stack_symbol)),
                StackSymbol(SymbolOrEpsilon::Symbol(initial_stack_symbol.clone())),
            ],
            self.start_state,
        );

        self.start_state = initial_state_id;

        let accepting_state = State::with_name("t");
        let accepting_state_id = accepting_state.id();

        for state in old_states.keys().copied() {
            self.link(
                state,
                TapeSymbol(SymbolOrEpsilon::Epsilon),
                StackSymbol(SymbolOrEpsilon::Symbol(initial_stack_symbol.clone())),
                vec![StackSymbol(SymbolOrEpsilon::Symbol(
                    initial_stack_symbol.clone(),
                ))],
                accepting_state_id,
            );
        }

        self.states.insert(initial_state_id, initial_state);
        self.states.insert(accepting_state_id, accepting_state);
        self.make_final(accepting_state_id);

        self.acceptance_condition = AcceptanceCondition::FinalState.into();
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

    pub fn transitions(&self) -> Vec<(&str, String, String, String, &str)> {
        let mut transitions = Vec::new();
        for (from_state, to) in &self.transitions {
            let from_state = self
                .states
                .get(from_state)
                .unwrap()
                .name()
                .unwrap_or_else(|| "q?");

            for ((tape_symbol, popped_stack_symbol), to) in to {
                let tape_symbol = tape_symbol.to_string();
                let popped_stack_symbol = popped_stack_symbol.to_string();

                for (to_state, pushed_stack_symbols) in to {
                    let to_state = self.states.get(to_state).unwrap().name().unwrap_or("q?");
                    let pushed_stack_symbols = pushed_stack_symbols
                        .iter()
                        .map(|s| s.to_string())
                        .collect::<String>();

                    transitions.push((
                        from_state,
                        tape_symbol.clone(),
                        popped_stack_symbol.clone(),
                        pushed_stack_symbols,
                        to_state,
                    ));
                }
            }
        }

        transitions
    }
}

impl From<&ContextFreeGrammar> for PushdownAutomaton {
    fn from(cfg: &ContextFreeGrammar) -> Self {
        let alphabet = cfg
            .productions()
            .values()
            .flat_map(|words| {
                words.iter().flat_map(|word| {
                    word.0.iter().filter_map(|symbol| {
                        if let ProductionSymbol::Terminal(terminal) = symbol {
                            Some(terminal)
                        } else {
                            None
                        }
                    })
                })
            })
            .collect::<IndexSet<_>>();

        let mut pda = PushdownAutomaton::new(
            Some(State::with_name("q")),
            cfg.start_symbol().0.clone(),
            AcceptanceCondition::EmptyStack.into(),
        );

        for terminal in alphabet {
            pda.link(
                pda.start_state,
                TapeSymbol(SymbolOrEpsilon::Symbol(terminal.0.clone())),
                StackSymbol(SymbolOrEpsilon::Symbol(terminal.0.clone())),
                vec![StackSymbol(SymbolOrEpsilon::Epsilon)],
                pda.start_state,
            );
        }

        for (lhs, rhs) in cfg.productions() {
            let lhs = &lhs.0;

            for word in rhs {
                pda.link(
                    pda.start_state,
                    TapeSymbol(SymbolOrEpsilon::Epsilon),
                    StackSymbol(SymbolOrEpsilon::Symbol(lhs.clone())),
                    word.0
                        .iter()
                        .map(|symbol| {
                            let symbol = match symbol {
                                ProductionSymbol::Terminal(terminal) => &terminal.0,
                                ProductionSymbol::NonTerminal(non_terminal) => &non_terminal.0,
                            };

                            StackSymbol(SymbolOrEpsilon::Symbol(symbol.clone()))
                        })
                        .collect(),
                    pda.start_state,
                );
            }
        }

        for lhs in cfg.erasing_productions().iter() {
            let lhs = &lhs.0;

            pda.link(
                pda.start_state,
                TapeSymbol(SymbolOrEpsilon::Epsilon),
                StackSymbol(SymbolOrEpsilon::Symbol(lhs.clone())),
                vec![StackSymbol(SymbolOrEpsilon::Epsilon)],
                pda.start_state,
            );
        }

        pda
    }
}

impl From<&GreibachNormalFormGrammar> for PushdownAutomaton {
    fn from(gnf: &GreibachNormalFormGrammar) -> Self {
        let mut pda = PushdownAutomaton::new(
            Some(State::with_name("q")),
            gnf.start_symbol().0.clone(),
            AcceptanceCondition::EmptyStack.into(),
        );

        for (lhs, rhs) in gnf.productions() {
            let lhs = &lhs.0;

            for GnfWord(terminal, non_terminals) in rhs {
                let pushed_stack_symbols = non_terminals
                    .iter()
                    .map(|nt| StackSymbol(SymbolOrEpsilon::Symbol(nt.0.clone())))
                    .collect::<Vec<_>>();

                pda.link(
                    pda.start_state,
                    TapeSymbol(SymbolOrEpsilon::Symbol(terminal.0.clone())),
                    StackSymbol(SymbolOrEpsilon::Symbol(lhs.clone())),
                    if pushed_stack_symbols.is_empty() {
                        vec![StackSymbol(SymbolOrEpsilon::Epsilon)]
                    } else {
                        pushed_stack_symbols
                    },
                    pda.start_state,
                );
            }
        }

        if gnf.is_start_symbol_erasable() {
            pda.link(
                pda.start_state,
                TapeSymbol(SymbolOrEpsilon::Epsilon),
                StackSymbol(SymbolOrEpsilon::Symbol(gnf.start_symbol().0.clone())),
                vec![StackSymbol(SymbolOrEpsilon::Epsilon)],
                pda.start_state,
            );
        }

        pda
    }
}
