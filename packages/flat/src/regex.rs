use std::fmt::Display;

use indexmap::{IndexMap, IndexSet};
use winnow::{
    ascii::space0,
    combinator::{alt, delimited, eof, repeat, separated_foldr1, terminated},
    error::ContextError,
    token::one_of,
    Parser, Result, Stateful,
};

use crate::{automata::Dfa, language::Symbol};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RegularExpression {
    Zero,
    One,
    Symbol(Symbol),
    Union(Box<RegularExpression>, Box<RegularExpression>),
    Concatenation(Box<RegularExpression>, Box<RegularExpression>),
    KleeneStar(Box<RegularExpression>),
    Plus(Box<RegularExpression>),
}

impl RegularExpression {
    pub fn simplified(&self) -> RegularExpression {
        match self {
            RegularExpression::Zero | RegularExpression::One | RegularExpression::Symbol(_) => {
                self.clone()
            }
            RegularExpression::Union(box r1, box r2) => {
                let r1 = r1.simplified();
                let r2 = r2.simplified();

                if r1 == r2 {
                    return r1;
                }

                if r1 == RegularExpression::One {
                    if let RegularExpression::Plus(r) = r2.clone() {
                        return RegularExpression::KleeneStar(r.into());
                    }
                }

                if let RegularExpression::Concatenation(box r11, box r12) = r1.clone() {
                    if r11 == r2 {
                        return RegularExpression::Concatenation(
                            r2.into(),
                            RegularExpression::Union(r12.into(), RegularExpression::One.into())
                                .into(),
                        )
                        .simplified();
                    }

                    if r12 == r2 {
                        return RegularExpression::Concatenation(
                            RegularExpression::Union(r11.into(), RegularExpression::One.into())
                                .into(),
                            r2.into(),
                        )
                        .simplified();
                    }
                }

                if let RegularExpression::Concatenation(box r21, box r22) = r2.clone() {
                    if r21 == r1 {
                        return RegularExpression::Concatenation(
                            r1.into(),
                            RegularExpression::Union(RegularExpression::One.into(), r22.into())
                                .into(),
                        )
                        .simplified();
                    }

                    if r22 == r1 {
                        return RegularExpression::Concatenation(
                            RegularExpression::Union(RegularExpression::One.into(), r21.into())
                                .into(),
                            r1.into(),
                        )
                        .simplified();
                    }
                }

                if let RegularExpression::Concatenation(box r11, box r12) = r1.clone() {
                    if let RegularExpression::Concatenation(box r21, box r22) = r2.clone() {
                        if r11 == r21 {
                            return RegularExpression::Concatenation(
                                r11.into(),
                                RegularExpression::Union(r12.into(), r22.into()).into(),
                            )
                            .simplified();
                        }

                        if r12 == r22 {
                            return RegularExpression::Concatenation(
                                RegularExpression::Union(r11.into(), r21.into()).into(),
                                r12.into(),
                            )
                            .simplified();
                        }
                    }
                }

                return RegularExpression::Union(Box::new(r1), Box::new(r2));
            }
            RegularExpression::Concatenation(box r1, box r2) => {
                let r1 = r1.simplified();
                let r2 = r2.simplified();

                if r1 == RegularExpression::One {
                    return r2;
                }
                if r2 == RegularExpression::One {
                    return r1;
                }

                if let RegularExpression::KleeneStar(box r) = r1.clone() {
                    if r2 == r
                        || r2
                            == RegularExpression::Union(
                                RegularExpression::One.into(),
                                r.clone().into(),
                            )
                        || r2
                            == RegularExpression::Union(
                                r.clone().into(),
                                RegularExpression::One.into(),
                            )
                    {
                        return RegularExpression::Plus(r.into());
                    }
                }

                if let RegularExpression::KleeneStar(box r) = r2.clone() {
                    if r1 == r
                        || r1
                            == RegularExpression::Union(
                                RegularExpression::One.into(),
                                r.clone().into(),
                            )
                        || r1
                            == RegularExpression::Union(
                                r.clone().into(),
                                RegularExpression::One.into(),
                            )
                    {
                        return RegularExpression::Plus(r.into());
                    }
                }

                return RegularExpression::Concatenation(Box::new(r1), Box::new(r2));
            }
            RegularExpression::KleeneStar(box r) => {
                let r = r.simplified();

                if r == RegularExpression::One {
                    return RegularExpression::One;
                }

                if let RegularExpression::KleeneStar(_) = r {
                    return r;
                }

                if let RegularExpression::Union(box r1, box r2) = r.clone() {
                    if r1 == RegularExpression::One {
                        return RegularExpression::KleeneStar(r2.into());
                    }
                    if r2 == RegularExpression::One {
                        return RegularExpression::KleeneStar(r1.into());
                    }
                }

                // if let RegularExpression::Plus(_) = r {
                //     return RegularExpression::KleeneStar(Box::new(r));
                // }

                return RegularExpression::KleeneStar(Box::new(r));
            }
            _ => self.clone(),
        }
    }

    fn stringify(&self, parent: Option<&str>) -> String {
        match self {
            RegularExpression::Zero => "0".to_string(),
            RegularExpression::One => "1".to_string(),
            RegularExpression::Symbol(symbol) => symbol.to_string(),
            RegularExpression::Union(left, right) => {
                let s = format!(
                    "{} + {}",
                    left.stringify(Some("+")),
                    right.stringify(Some("+"))
                );

                match parent {
                    None | Some("+") => s,
                    _ => format!("({})", s),
                }
            }
            RegularExpression::Concatenation(left, right) => {
                let s = format!(
                    "{}{}",
                    left.stringify(Some("*")),
                    right.stringify(Some("*"))
                );

                match parent {
                    None | Some("*") | Some("+") => s,
                    _ => format!("({})", s),
                }
            }
            RegularExpression::KleeneStar(expr) => {
                let s = format!("{}^*", expr.stringify(Some("^*")));
                match parent {
                    None | Some("*") | Some("+") => s,
                    _ => format!("({})", s),
                }
            }
            RegularExpression::Plus(expr) => {
                let s = format!("{}^+", expr.stringify(Some("^+")));
                match parent {
                    None | Some("*") | Some("+") => s,
                    _ => format!("({})", s),
                }
            }
        }
    }

    pub fn from_dfa(
        dfa: Dfa,
    ) -> (
        RegularExpression,
        IndexMap<(usize, usize, usize), RegularExpression>,
    ) {
        let mut ordered_states = IndexSet::with_capacity(dfa.states.len());
        let mut stack = vec![dfa.start_state];

        // Name states in order of traversal
        while let Some(state) = stack.pop() {
            if ordered_states.insert(state) {
                ordered_states.insert(state);

                if let Some(transitions) = dfa.transitions.get(&state) {
                    for &next_state in transitions.values() {
                        stack.push(next_state);
                    }
                }
            }
        }

        for &state in dfa.states.keys() {
            ordered_states.insert(state);
        }

        let get_symbols = |from: usize, to: usize| {
            let from_state = ordered_states[from - 1];
            let to_state = ordered_states[to - 1];

            let mut symbols = IndexSet::new();
            if let Some(transitions) = dfa.transitions.get(&from_state) {
                for (symbol, &next_state) in transitions {
                    if next_state == to_state {
                        symbols.insert(symbol.clone());
                    }
                }
            }

            symbols
        };

        let mut intermediary_regexes = IndexMap::new();

        fn regex_intermediary_states_impl<F: Fn(usize, usize) -> IndexSet<Symbol>>(
            from: usize,
            to: usize,
            max_intermediary: usize,
            get_symbols: &F,
            intermediary_regexes: &mut IndexMap<(usize, usize, usize), RegularExpression>,
        ) -> RegularExpression {
            if max_intermediary == 0 {
                let symbols = get_symbols(from, to);
                let symbols = symbols
                    .iter()
                    .map(|symbol| RegularExpression::Symbol(symbol.clone()));

                return if from == to {
                    symbols.fold(RegularExpression::One, |acc, symbol| {
                        RegularExpression::Union(Box::new(acc), Box::new(symbol))
                    })
                } else {
                    symbols
                        .reduce(|left, right| {
                            RegularExpression::Union(Box::new(left), Box::new(right))
                        })
                        .unwrap_or(RegularExpression::Zero)
                };
            }

            let first = regex_intermediary_states(
                from,
                to,
                max_intermediary - 1,
                get_symbols,
                intermediary_regexes,
            );

            let rise = regex_intermediary_states(
                from,
                max_intermediary,
                max_intermediary - 1,
                get_symbols,
                intermediary_regexes,
            );
            if rise == RegularExpression::Zero {
                return first;
            }

            let loop_ = regex_intermediary_states(
                max_intermediary,
                max_intermediary,
                max_intermediary - 1,
                get_symbols,
                intermediary_regexes,
            );
            let fall = regex_intermediary_states(
                max_intermediary,
                to,
                max_intermediary - 1,
                get_symbols,
                intermediary_regexes,
            );
            if fall == RegularExpression::Zero {
                return first;
            }

            let second = RegularExpression::Concatenation(
                RegularExpression::Concatenation(
                    rise.into(),
                    RegularExpression::KleeneStar(loop_.into()).into(),
                )
                .into(),
                fall.into(),
            );

            RegularExpression::Union(first.into(), second.into())
        }

        fn regex_intermediary_states<F: Fn(usize, usize) -> IndexSet<Symbol>>(
            from: usize,
            to: usize,
            max_intermediary: usize,
            get_symbols: &F,
            intermediary_regexes: &mut IndexMap<(usize, usize, usize), RegularExpression>,
        ) -> RegularExpression {
            if let Some(regex) = intermediary_regexes.get(&(from, to, max_intermediary)) {
                return regex.clone();
            }

            let regex = regex_intermediary_states_impl(
                from,
                to,
                max_intermediary,
                get_symbols,
                intermediary_regexes,
            )
            .simplified();
            intermediary_regexes.insert((from, to, max_intermediary), regex.clone());
            regex
        }

        let r = dfa
            .final_states
            .iter()
            .map(|state| {
                let state_idx = ordered_states.get_index_of(state).unwrap() + 1;
                regex_intermediary_states(
                    1,
                    state_idx,
                    ordered_states.len(),
                    &get_symbols,
                    &mut intermediary_regexes,
                )
            })
            .reduce(|left, right| RegularExpression::Union(Box::new(left), Box::new(right)))
            .unwrap_or(RegularExpression::Zero);

        (r, intermediary_regexes)
    }
}

impl Display for RegularExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.stringify(None))
    }
}

impl TryFrom<&str> for RegularExpression {
    type Error = String;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        parse_regular_expression(value)
    }
}

impl From<Dfa> for RegularExpression {
    fn from(dfa: Dfa) -> Self {
        RegularExpression::from_dfa(dfa).0
    }
}

#[derive(Debug)]
struct State {}

type Input<'a> = Stateful<&'a str, State>;

fn parse_regular_expression(input: &str) -> Result<RegularExpression, String> {
    let mut parser = terminated(regular_expression, eof);

    let state = State {};
    let mut parser_input = Stateful { input, state };

    let result = parser
        .parse_next(&mut parser_input)
        .map_err(|_| format!("Failed to parse regular expression: \"{input}\""));

    result
}

fn regular_expression(input: &mut Input) -> Result<RegularExpression> {
    union.parse_next(input)
}

fn union(input: &mut Input) -> Result<RegularExpression> {
    separated_foldr1(concatenation, spaced('+'), |left, _, right| {
        RegularExpression::Union(Box::new(left), Box::new(right))
    })
    .parse_next(input)
}

fn concatenation(input: &mut Input) -> Result<RegularExpression> {
    repeat(1.., concat_expression)
        .map(|children: Vec<RegularExpression>| {
            children
                .into_iter()
                .rev()
                .reduce(|right, left| {
                    RegularExpression::Concatenation(Box::new(left), Box::new(right))
                })
                .unwrap()
        })
        .parse_next(input)
}

fn parenthesized_expression(input: &mut Input) -> Result<RegularExpression> {
    delimited('(', regular_expression, ')').parse_next(input)
}

fn concat_expression(input: &mut Input) -> Result<RegularExpression> {
    alt((
        kleene_star,
        plus,
        parenthesized_expression,
        symbol,
        zero,
        one,
    ))
    .parse_next(input)
}

fn base_expression(input: &mut Input) -> Result<RegularExpression> {
    alt((parenthesized_expression, symbol, zero, one)).parse_next(input)
}

fn kleene_star(input: &mut Input) -> Result<RegularExpression> {
    (base_expression, "^*")
        .map(|(expr, _)| RegularExpression::KleeneStar(Box::new(expr)))
        .parse_next(input)
}

fn plus(input: &mut Input) -> Result<RegularExpression> {
    (base_expression, "^+")
        .map(|(expr, _)| RegularExpression::Plus(Box::new(expr)))
        .parse_next(input)
}

fn symbol(input: &mut Input) -> Result<RegularExpression> {
    one_of('a'..='z')
        .map(|c: char| RegularExpression::Symbol(Symbol::new(c.to_string())))
        .parse_next(input)
}

fn one(input: &mut Input) -> Result<RegularExpression> {
    '1'.map(|_| RegularExpression::One).parse_next(input)
}

fn zero(input: &mut Input) -> Result<RegularExpression> {
    '0'.map(|_| RegularExpression::Zero).parse_next(input)
}

fn spaced<'a, T>(
    parser: impl Parser<Input<'a>, T, ContextError>,
) -> impl Parser<Input<'a>, T, ContextError> {
    delimited(space0, parser, space0)
}
