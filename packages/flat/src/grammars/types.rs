use std::{borrow::Cow, fmt::Display, hash::Hash};

use derive_more::Display;
use indexmap::{IndexMap, IndexSet};

use crate::language::{Symbol, Word, EPSILON};

#[derive(Debug, Display, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Terminal(pub Symbol);

#[derive(Debug, Display, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NonTerminal(pub Symbol);

#[derive(Debug, Display, Clone, PartialEq, Eq, Hash)]
pub enum ProductionSymbol {
    Terminal(Terminal),
    NonTerminal(NonTerminal),
}

pub trait ProductionWord: Display + Clone + TryFrom<Word<ProductionSymbol>> {
    fn to_word(&self) -> Word<ProductionSymbol>;
}

impl TryFrom<Word<ProductionSymbol>> for NonTerminal {
    type Error = String;

    fn try_from(value: Word<ProductionSymbol>) -> Result<Self, Self::Error> {
        if value.0.len() == 1 {
            if let ProductionSymbol::NonTerminal(nt) = &value.0[0] {
                Ok(nt.clone())
            } else {
                Err("Expected a non-terminal".to_string())
            }
        } else {
            Err("Expected a single non-terminal".to_string())
        }
    }
}

impl TryFrom<Word<ProductionSymbol>> for Terminal {
    type Error = String;

    fn try_from(value: Word<ProductionSymbol>) -> Result<Self, Self::Error> {
        if value.0.len() == 1 {
            if let ProductionSymbol::Terminal(t) = &value.0[0] {
                Ok(t.clone())
            } else {
                Err("Expected a terminal".to_string())
            }
        } else {
            Err("Expected a single terminal".to_string())
        }
    }
}

impl ProductionWord for NonTerminal {
    fn to_word(&self) -> Word<ProductionSymbol> {
        Word(vec![ProductionSymbol::NonTerminal(self.clone())])
    }
}

impl ProductionWord for Terminal {
    fn to_word(&self) -> Word<ProductionSymbol> {
        Word(vec![ProductionSymbol::Terminal(self.clone())])
    }
}

impl ProductionWord for Word<ProductionSymbol> {
    fn to_word(&self) -> Word<ProductionSymbol> {
        Word(self.0.clone())
    }
}

pub trait Grammar<L: ProductionWord, R: ProductionWord> {
    fn new(start_symbol: NonTerminal) -> Self;

    fn start_symbol(&self) -> &NonTerminal;
    fn erasing_productions(&self) -> Cow<'_, IndexSet<L>>;
    fn productions(&self) -> &IndexMap<L, IndexSet<R>>;

    fn add_erasing_production(&mut self, lhs: impl TryInto<L>);
    fn add_production(&mut self, lhs: impl TryInto<L>, rhs: impl TryInto<R>);

    fn from_productions<S: AsRef<str>>(start_symbol: S, productions: &[impl AsRef<str>]) -> Self
    where
        Self: Sized,
    {
        let start_symbol = NonTerminal(Symbol::new(start_symbol.as_ref()));
        let mut grammar = Self::new(start_symbol);

        for production in productions {
            let parts = production
                .as_ref()
                .split("→")
                .map(|part| part.trim())
                .collect::<Vec<_>>();
            if parts.len() != 2 {
                panic!("Invalid production format");
            }

            let lhs = Word(
                parts[0]
                    .chars()
                    .map(|c| {
                        if c.is_ascii_uppercase() {
                            ProductionSymbol::NonTerminal(NonTerminal(Symbol::new(c)))
                        } else {
                            ProductionSymbol::Terminal(Terminal(Symbol::new(c)))
                        }
                    })
                    .collect(),
            );
            parts[1].split("|").for_each(|rhs| {
                let rhs = rhs.trim();
                if rhs == EPSILON {
                    grammar.add_erasing_production(lhs.clone());
                } else {
                    let word = Word(
                        rhs.chars()
                            .map(|c| {
                                if c.is_ascii_uppercase() {
                                    ProductionSymbol::NonTerminal(NonTerminal(Symbol::new(c)))
                                } else {
                                    ProductionSymbol::Terminal(Terminal(Symbol::new(c)))
                                }
                            })
                            .collect(),
                    );

                    grammar.add_production(lhs.clone(), word.clone());
                }
            })
        }

        grammar
    }

    fn definition(&self) -> String {
        let start_symbol = self.start_symbol();
        let erasing_productions = self.erasing_productions();
        let productions = self.productions();

        let mut string_productions =
            IndexMap::with_capacity(productions.len() + erasing_productions.len());

        let mut words = IndexSet::new();

        for lhs in erasing_productions.as_ref() {
            string_productions
                .entry(lhs.to_string())
                .or_insert_with(Vec::new)
                .push(EPSILON.to_owned());

            words.insert(lhs.to_word());
        }

        for (lhs, rhs) in productions {
            string_productions
                .entry(lhs.to_string())
                .or_insert_with(Vec::new)
                .extend(rhs.iter().map(|word| word.to_string()));

            words.insert(lhs.to_word());
            words.extend(rhs.iter().map(|word| word.to_word()));
        }

        let mut non_terminals = IndexSet::from([start_symbol.clone()]);
        let mut terminals = IndexSet::new();

        for word in words {
            for symbol in word.0 {
                match symbol {
                    ProductionSymbol::Terminal(t) => {
                        terminals.insert(t);
                    }
                    ProductionSymbol::NonTerminal(nt) => {
                        non_terminals.insert(nt);
                    }
                }
            }
        }

        non_terminals.sort_by(|a, b| {
            if a == start_symbol {
                return std::cmp::Ordering::Less;
            }
            if b == start_symbol {
                return std::cmp::Ordering::Greater;
            }
            a.cmp(b)
        });
        terminals.sort();

        string_productions.sort_by(|lhs1, _, lhs2, _| lhs1.cmp(lhs2));

        let mut definition = format!(
            "G = ({{{}}}, {{{}}}, P, {})\n\n",
            non_terminals
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", "),
            terminals
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", "),
            start_symbol
        );

        definition += "P = {\n";

        for (lhs, rhs) in string_productions {
            definition += &format!("  {} → {}\n", lhs, rhs.join(" | "));
        }

        definition += "}\n";

        definition
    }
}
