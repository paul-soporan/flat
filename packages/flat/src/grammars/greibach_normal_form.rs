use std::{borrow::Cow, fmt::Display};

use indexmap::{indexset, IndexMap, IndexSet};

use crate::{
    grammars::{
        chomsky_normal_form::{ChomskyNormalFormGrammar, CnfWord},
        context_free::ContextFreeGrammar,
        types::{Grammar, NonTerminal, ProductionSymbol, ProductionWord, Terminal, Word},
    },
    language::Symbol,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GnfWord(Terminal, Vec<NonTerminal>);

impl Display for GnfWord {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}{}",
            self.0,
            self.1.iter().map(ToString::to_string).collect::<String>()
        )
    }
}

impl TryFrom<Word<ProductionSymbol>> for GnfWord {
    type Error = String;

    fn try_from(value: Word<ProductionSymbol>) -> Result<Self, Self::Error> {
        if value.0.is_empty() {
            return Err("GNF word cannot be empty".to_string());
        }

        let terminal = match &value.0[0] {
            ProductionSymbol::Terminal(t) => t.clone(),
            _ => return Err("First symbol must be a terminal".to_string()),
        };

        let non_terminals = value
            .0
            .iter()
            .skip(1)
            .filter_map(|s| match s {
                ProductionSymbol::NonTerminal(nt) => Some(nt.clone()),
                _ => None,
            })
            .collect();

        Ok(GnfWord(terminal, non_terminals))
    }
}

impl ProductionWord for GnfWord {
    fn to_word(&self) -> Word<ProductionSymbol> {
        let mut symbols = vec![ProductionSymbol::Terminal(self.0.clone())];
        symbols.extend(
            self.1
                .iter()
                .map(|nt| ProductionSymbol::NonTerminal(nt.clone())),
        );
        Word(symbols)
    }
}

#[derive(Debug)]
pub struct GreibachNormalFormGrammar {
    start_symbol: NonTerminal,
    is_start_symbol_erasable: bool,
    productions: IndexMap<NonTerminal, IndexSet<GnfWord>>,
}

impl Grammar<NonTerminal, GnfWord> for GreibachNormalFormGrammar {
    fn new(start_symbol: NonTerminal) -> Self {
        Self {
            start_symbol,
            is_start_symbol_erasable: false,
            productions: IndexMap::new(),
        }
    }

    fn start_symbol(&self) -> &NonTerminal {
        &self.start_symbol
    }

    fn erasing_productions(&self) -> Cow<'_, IndexSet<NonTerminal>> {
        Cow::Owned(if self.is_start_symbol_erasable {
            indexset! {self.start_symbol.clone()}
        } else {
            IndexSet::new()
        })
    }

    fn productions(&self) -> &IndexMap<NonTerminal, IndexSet<GnfWord>> {
        &self.productions
    }

    fn add_erasing_production(&mut self, lhs: impl TryInto<NonTerminal>) {
        let lhs = lhs.try_into().unwrap_or_else(|_| {
            panic!("Failed to convert to NonTerminal");
        });

        if lhs != self.start_symbol {
            panic!("Only the start symbol can be an erasing production in GNF");
        }

        self.is_start_symbol_erasable = true;
    }

    fn add_production(&mut self, lhs: impl TryInto<NonTerminal>, rhs: impl TryInto<GnfWord>) {
        let lhs = lhs.try_into().unwrap_or_else(|_| {
            panic!("Failed to convert to NonTerminal");
        });
        let rhs = rhs.try_into().unwrap_or_else(|_| {
            panic!("Failed to convert to GnfWord");
        });

        self.productions
            .entry(lhs)
            .or_insert_with(IndexSet::new)
            .insert(rhs);
    }
}

impl GreibachNormalFormGrammar {
    pub fn from_chomsky_normal_form(cnf: &ChomskyNormalFormGrammar) -> Self {
        let non_terminals = cnf
            .productions
            .keys()
            .cloned()
            .enumerate()
            .map(|(i, nt)| (nt, NonTerminal(Symbol::new(format!("A_{}", i + 1)))))
            .collect::<IndexMap<_, _>>();

        let mut cfg = ContextFreeGrammar {
            start_symbol: non_terminals[&cnf.start_symbol].clone(),
            erasing_productions: if cnf.is_start_symbol_erasable {
                indexset! {non_terminals[&cnf.start_symbol].clone()}
            } else {
                IndexSet::new()
            },
            productions: cnf
                .productions
                .iter()
                .map(|(lhs, rhs)| {
                    (
                        non_terminals[lhs].clone(),
                        rhs.into_iter()
                            .map(|word| {
                                Word(match word {
                                    CnfWord::Terminal(t) => {
                                        vec![ProductionSymbol::Terminal(t.clone())]
                                    }
                                    CnfWord::NonTerminals(nt1, nt2) => {
                                        let nt1 = non_terminals[nt1].clone();
                                        let nt2 = non_terminals[nt2].clone();

                                        vec![
                                            ProductionSymbol::NonTerminal(nt1),
                                            ProductionSymbol::NonTerminal(nt2),
                                        ]
                                    }
                                })
                            })
                            .collect(),
                    )
                })
                .collect(),
        };

        let mut auxiliary_non_terminals = IndexSet::new();

        for (i, nt) in non_terminals.values().enumerate() {
            if let Some(rhs) = cfg.productions.get(nt) {
                let mut rhs = rhs.clone();
                let mut next_rhs = IndexSet::new();

                let mut left_linear_trails = IndexSet::new();

                loop {
                    let mut changed = false;

                    'outer: for word in rhs {
                        if let Some(ProductionSymbol::NonTerminal(child_nt)) = word.0.first() {
                            let j = non_terminals.values().position(|v| v == child_nt).unwrap();
                            if j < i {
                                if let Some(child_productions) = cfg.productions.get(child_nt) {
                                    next_rhs.extend(child_productions.iter().map(|child_word| {
                                        let mut new_word = child_word.clone();
                                        new_word.0.extend(word.0[1..].to_vec());
                                        new_word
                                    }));
                                    changed = true;

                                    continue 'outer;
                                }
                            } else if j == i {
                                left_linear_trails.insert(word.0[1..].to_vec());

                                continue 'outer;
                            }
                        }

                        next_rhs.insert(word);
                    }

                    rhs = next_rhs;
                    next_rhs = IndexSet::new();

                    if !changed {
                        break;
                    }
                }

                if left_linear_trails.is_empty() {
                    cfg.productions.insert(nt.clone(), rhs);
                } else {
                    let new_nt = NonTerminal(Symbol::new(format!("B_{}", i + 1)));
                    auxiliary_non_terminals.insert(new_nt.clone());

                    cfg.productions.insert(
                        new_nt.clone(),
                        left_linear_trails
                            .into_iter()
                            .flat_map(|trail| {
                                let mut new_word = trail.clone();
                                new_word.push(ProductionSymbol::NonTerminal(new_nt.clone()));

                                vec![Word(trail), Word(new_word)]
                            })
                            .collect(),
                    );

                    cfg.productions.insert(
                        nt.clone(),
                        rhs.into_iter()
                            .flat_map(|word| {
                                let mut new_word = word.clone();
                                new_word
                                    .0
                                    .push(ProductionSymbol::NonTerminal(new_nt.clone()));

                                vec![word, new_word]
                            })
                            .collect(),
                    );
                }
            }
        }

        let mut gnf = Self {
            start_symbol: cfg.start_symbol.clone(),
            is_start_symbol_erasable: cfg.erasing_productions.contains(&cfg.start_symbol),
            productions: IndexMap::new(),
        };

        for nt in non_terminals.values().rev() {
            if let Some(rhs) = cfg.productions.get(nt) {
                let mut next_rhs = IndexSet::new();
                for word in rhs {
                    if let Some(ProductionSymbol::NonTerminal(child_nt)) = word.0.first()
                        && let Some(child_productions) = gnf.productions.get(child_nt)
                    {
                        next_rhs.extend(child_productions.iter().map(
                            |GnfWord(terminal, non_terminals)| {
                                let mut non_terminals = non_terminals.clone();
                                non_terminals.extend(word.0[1..].iter().map(|nt| match nt {
                                    ProductionSymbol::NonTerminal(nt) => nt.clone(),
                                    _ => panic!("Expected a non-terminal"),
                                }));

                                GnfWord(terminal.clone(), non_terminals)
                            },
                        ));
                    } else {
                        let mut word = word.clone();
                        let non_terminals = word.0.split_off(1);

                        next_rhs.insert(GnfWord(
                            match &word.0[0] {
                                ProductionSymbol::Terminal(t) => t.clone(),
                                _ => {
                                    panic!("Expected a terminal")
                                }
                            },
                            non_terminals
                                .into_iter()
                                .map(|nt| match nt {
                                    ProductionSymbol::NonTerminal(nt) => nt,
                                    _ => panic!("Expected a non-terminal"),
                                })
                                .collect(),
                        ));
                    }
                }

                gnf.productions.insert(nt.clone(), next_rhs);
            }
        }

        for nt in auxiliary_non_terminals {
            if let Some(rhs) = cfg.productions.get(&nt) {
                let mut next_rhs = IndexSet::new();
                for word in rhs {
                    if let Some(ProductionSymbol::NonTerminal(child_nt)) = word.0.first()
                        && let Some(child_productions) = gnf.productions.get(child_nt)
                    {
                        next_rhs.extend(child_productions.iter().map(
                            |GnfWord(terminal, non_terminals)| {
                                let mut non_terminals = non_terminals.clone();
                                non_terminals.extend(word.0[1..].iter().map(|nt| match nt {
                                    ProductionSymbol::NonTerminal(nt) => nt.clone(),
                                    _ => panic!("Expected a non-terminal"),
                                }));

                                GnfWord(terminal.clone(), non_terminals)
                            },
                        ));
                    } else {
                        let mut word = word.clone();
                        let non_terminals = word.0.split_off(1);

                        next_rhs.insert(GnfWord(
                            match &word.0[0] {
                                ProductionSymbol::Terminal(t) => t.clone(),
                                _ => {
                                    panic!("Expected a terminal")
                                }
                            },
                            non_terminals
                                .into_iter()
                                .map(|nt| match nt {
                                    ProductionSymbol::NonTerminal(nt) => nt,
                                    _ => panic!("Expected a non-terminal"),
                                })
                                .collect(),
                        ));
                    }
                }

                gnf.productions.insert(nt.clone(), next_rhs);
            }
        }

        gnf
    }

    // pub fn to_context_free_grammar(&self) -> ContextFreeGrammar {
    //     let mut cfg = ContextFreeGrammar {
    //         start_symbol: self.start_symbol.clone(),
    //         erasing_productions: if self.is_start_symbol_erasable {
    //             indexset! {self.start_symbol.clone()}
    //         } else {
    //             IndexSet::new()
    //         },
    //         productions: IndexMap::new(),
    //     };

    //     for (lhs, rhs) in &self.productions {
    //         let entry = cfg
    //             .productions
    //             .entry(lhs.clone())
    //             .or_insert_with(IndexSet::new);

    //         for (terminal, non_terminals) in rhs {
    //             entry.insert(Word(
    //                 std::iter::once(ProductionSymbol::Terminal(terminal.clone()))
    //                     .chain(
    //                         non_terminals
    //                             .iter()
    //                             .cloned()
    //                             .map(|nt| ProductionSymbol::NonTerminal(nt)),
    //                     )
    //                     .collect(),
    //             ));
    //         }
    //     }

    //     cfg
    // }
}
