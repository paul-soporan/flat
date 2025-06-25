use std::{collections::VecDeque, fmt::Display};

use indexmap::{indexmap, IndexMap, IndexSet};
use itertools::Itertools;

use crate::{
    automata::types::{Automaton, State, StateId},
    language::{Symbol, Word},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum TapeHeadMovement {
    Left,
    Right,
}

const BLANK_SYMBOL: &str = "B";

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum TapeSymbol {
    Blank,
    Symbol(Symbol),
}

impl Display for TapeSymbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TapeSymbol::Blank => write!(f, "{}", BLANK_SYMBOL),
            TapeSymbol::Symbol(symbol) => write!(f, "{}", symbol),
        }
    }
}

#[derive(Debug, Clone)]
struct Tape {
    cells: VecDeque<TapeSymbol>,
    head_position: i32,
}

impl Tape {
    fn new(symbols: impl IntoIterator<Item = TapeSymbol>) -> Self {
        Self {
            cells: VecDeque::from_iter(symbols),
            head_position: 0,
        }
    }

    fn grow(&mut self) {
        if self.head_position < 0 {
            let blank_count = (-self.head_position) as usize;

            self.cells.reserve(blank_count);

            // Extend the tape to the left
            for _ in 0..blank_count {
                self.cells.push_front(TapeSymbol::Blank);
            }

            self.head_position = 0;
        } else if self.head_position >= self.cells.len() as i32 {
            let blank_count = (self.head_position - self.cells.len() as i32 + 1) as usize;

            self.cells.reserve(blank_count);

            // Extend the tape to the right
            for _ in 0..blank_count {
                self.cells.push_back(TapeSymbol::Blank);
            }
        }
    }

    fn read(&self) -> &TapeSymbol {
        if self.head_position < 0 || self.head_position >= self.cells.len() as i32 {
            &TapeSymbol::Blank
        } else {
            &self.cells[self.head_position as usize]
        }
    }

    fn write(&mut self, symbol: TapeSymbol) {
        self.grow();

        self.cells[self.head_position as usize] = symbol;
    }

    fn move_head(&mut self, movement: TapeHeadMovement) {
        match movement {
            TapeHeadMovement::Left => self.head_position -= 1,
            TapeHeadMovement::Right => self.head_position += 1,
        }
    }
}

#[derive(Debug)]
struct InstantaneousDescription<'a> {
    turing_machine: &'a TuringMachine,
    tape: Tape,
    state: StateId,
}

impl<'a> InstantaneousDescription<'a> {
    fn initial(
        turing_machine: &'a TuringMachine,
        tape_symbols: impl IntoIterator<Item = TapeSymbol>,
    ) -> Self {
        Self {
            turing_machine,
            tape: Tape::new(tape_symbols),
            state: turing_machine.start_state,
        }
    }

    fn is_final(&self) -> bool {
        self.turing_machine.final_states.contains(&self.state)
    }

    fn make_move(&mut self) -> bool {
        let current_symbol = self.tape.read();

        if let Some((new_state, new_symbol, movement)) = self
            .turing_machine
            .transitions
            .get(&self.state)
            .and_then(|transitions| transitions.get(current_symbol))
            .cloned()
        {
            self.tape.write(new_symbol);
            self.tape.move_head(movement);
            self.state = new_state;

            true
        } else {
            false
        }
    }
}

impl Display for InstantaneousDescription<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut tape = self.tape.clone();
        tape.grow();

        let mut symbols = tape
            .cells
            .iter()
            .map(ToString::to_string)
            .collect::<VecDeque<_>>();

        let current_state = self.turing_machine.states.get(&self.state).unwrap();

        symbols.insert(
            tape.head_position as usize,
            format!("{}", current_state.name().unwrap_or_else(|| "q?")),
        );

        while symbols.front() == Some(&BLANK_SYMBOL.to_string()) {
            symbols.pop_front();
        }

        while symbols.back() == Some(&BLANK_SYMBOL.to_string())
            && symbols.len() > (tape.head_position + 1) as usize
        {
            symbols.pop_back();
        }

        write!(f, "{}", symbols.iter().join(""))
    }
}

#[derive(Debug)]
pub struct Run {
    input: String,
    accepted: bool,
    instantaneous_descriptions: Vec<String>,
}

impl Run {
    pub fn accepted(&self) -> bool {
        self.accepted
    }

    fn add_id(&mut self, id: &InstantaneousDescription) {
        self.instantaneous_descriptions.push(id.to_string());
    }
}

impl Display for Run {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Let M be the turing machine.\n")?;
        writeln!(f, "w = {}\n", self.input)?;

        writeln!(
            f,
            r#"<style>
                .strikethrough {{
                    position: relative;
                }}

                .strikethrough:before {{
                    position: absolute;
                    content: "";
                    left: 0;
                    top: 50%;
                    right: 0;
                    border-top: 1px solid;
                    border-color: inherit;
                    transform:rotate(-60deg);
                }}
            </style>"#
        )?;

        writeln!(f, "The run of M on w:\n")?;
        write!(
            f,
            "{}",
            self.instantaneous_descriptions.join("  ↦<sub>M</sub>  ")
        )?;

        if !self.accepted {
            write!(f, "  <span class=\"strikethrough\">↦</span><sub>M</sub>")?;
        }

        writeln!(
            f,
            "\n\nThe run halts in a {} state of M, thus {}.",
            if self.accepted { "final" } else { "non-final" },
            if self.accepted {
                "w ∈ L(M)"
            } else {
                "w ∉ L(M)"
            }
        )?;

        Ok(())
    }
}

#[derive(Debug)]
pub struct TuringMachine {
    states: IndexMap<StateId, State>,
    start_state: StateId,
    final_states: IndexSet<StateId>,
    transitions: IndexMap<StateId, IndexMap<TapeSymbol, (StateId, TapeSymbol, TapeHeadMovement)>>,
}

impl Automaton for TuringMachine {
    fn make_final(&mut self, state: StateId) {
        self.final_states.insert(state);
    }
}

impl TuringMachine {
    pub fn new(start_state: Option<State>) -> Self {
        let start_state = start_state.unwrap_or_default();
        let start_state_id = start_state.id();

        Self {
            start_state: start_state_id,
            states: indexmap! { start_state_id => start_state },
            final_states: IndexSet::new(),
            transitions: IndexMap::new(),
        }
    }

    fn link(
        &mut self,
        from: StateId,
        read_symbol: TapeSymbol,
        written_symbol: TapeSymbol,
        movement: TapeHeadMovement,
        to: StateId,
    ) {
        self.transitions
            .entry(from)
            .or_insert_with(IndexMap::new)
            .insert(read_symbol, (to, written_symbol, movement));
    }

    pub fn from_definition(
        start_state: &str,
        final_states: &[&str],
        transitions: &[(&str, &str, &str, i32, &str)],
    ) -> Self {
        let mut state_map = IndexMap::new();

        let mut tm = Self::new(Some(State::with_name(start_state)));
        state_map.insert(start_state.to_string(), tm.start_state);

        for &final_state in final_states {
            let state = state_map.entry(final_state.to_string()).or_insert_with(|| {
                let state = State::with_name(final_state);
                let id = state.id();
                tm.states.insert(id, state);
                id
            });

            tm.make_final(*state);
        }

        fn parse_symbol(symbol: &str) -> TapeSymbol {
            if symbol == BLANK_SYMBOL {
                TapeSymbol::Blank
            } else {
                TapeSymbol::Symbol(Symbol::new(symbol.to_string()))
            }
        }

        for (from, read_symbol, written_symbol, movement, to) in transitions.iter().copied() {
            let from_state = *state_map.entry(from.to_string()).or_insert_with(|| {
                let state = State::with_name(from);
                let id = state.id();
                tm.states.insert(id, state);
                id
            });

            let read_symbol = parse_symbol(read_symbol);
            let written_symbol = parse_symbol(written_symbol);
            let movement = match movement {
                -1 => TapeHeadMovement::Left,
                1 => TapeHeadMovement::Right,
                _ => panic!("Invalid movement value: {}", movement),
            };

            let to_state = *state_map.entry(to.to_string()).or_insert_with(|| {
                let state = State::with_name(to);
                let id = state.id();
                tm.states.insert(id, state);
                id
            });

            tm.link(from_state, read_symbol, written_symbol, movement, to_state);
        }

        tm
    }

    pub fn run(&self, input: &Word<Symbol>) -> Run {
        let mut id = InstantaneousDescription::initial(
            self,
            input.clone().into_iter().map(|s| TapeSymbol::Symbol(s)),
        );

        let mut run = Run {
            input: input.to_string(),
            accepted: false,
            instantaneous_descriptions: Vec::new(),
        };

        loop {
            run.add_id(&id);

            if id.is_final() {
                run.accepted = true;
                return run;
            }

            if !id.make_move() {
                run.accepted = false;
                return run;
            }
        }
    }
}
