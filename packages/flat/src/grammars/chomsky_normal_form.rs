use std::{borrow::Cow, fmt::Display};

use indexmap::{indexset, IndexMap, IndexSet};
use itertools::Itertools;
use tabled::{builder::Builder, settings::Style};

use crate::{
    grammars::{
        context_free::ContextFreeGrammar,
        types::{Grammar, NonTerminal, ProductionSymbol, ProductionWord, Terminal, Word},
    },
    language::Symbol,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CnfWord {
    Terminal(Terminal),
    NonTerminals(NonTerminal, NonTerminal),
}

impl Display for CnfWord {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CnfWord::Terminal(t) => write!(f, "{t}"),
            CnfWord::NonTerminals(nt1, nt2) => write!(f, "{nt1}{nt2}"),
        }
    }
}

impl TryFrom<Word<ProductionSymbol>> for CnfWord {
    type Error = String;

    fn try_from(value: Word<ProductionSymbol>) -> Result<Self, Self::Error> {
        if value.0.len() == 1 {
            if let ProductionSymbol::Terminal(t) = &value.0[0] {
                Ok(CnfWord::Terminal(t.clone()))
            } else {
                Err("Expected a terminal".to_string())
            }
        } else if value.0.len() == 2 {
            if let (ProductionSymbol::NonTerminal(nt1), ProductionSymbol::NonTerminal(nt2)) =
                (&value.0[0], &value.0[1])
            {
                Ok(CnfWord::NonTerminals(nt1.clone(), nt2.clone()))
            } else {
                Err("Expected two non-terminals".to_string())
            }
        } else {
            Err(
                "CnfWord can only be created from a word with one terminal or two non-terminals"
                    .to_string(),
            )
        }
    }
}

impl ProductionWord for CnfWord {
    fn to_word(&self) -> Word<ProductionSymbol> {
        match self {
            CnfWord::Terminal(t) => Word(vec![ProductionSymbol::Terminal(t.clone())]),
            CnfWord::NonTerminals(nt1, nt2) => Word(vec![
                ProductionSymbol::NonTerminal(nt1.clone()),
                ProductionSymbol::NonTerminal(nt2.clone()),
            ]),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ChomskyNormalFormGrammar {
    pub(super) start_symbol: NonTerminal,
    pub(super) is_start_symbol_erasable: bool,
    pub(super) productions: IndexMap<NonTerminal, IndexSet<CnfWord>>,
}

impl Grammar<NonTerminal, CnfWord> for ChomskyNormalFormGrammar {
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

    fn productions(&self) -> &IndexMap<NonTerminal, IndexSet<CnfWord>> {
        &self.productions
    }

    fn add_erasing_production(&mut self, lhs: impl TryInto<NonTerminal>) {
        let lhs = lhs.try_into().unwrap_or_else(|_| {
            panic!("Failed to convert to NonTerminal");
        });

        if lhs != self.start_symbol {
            panic!("Only the start symbol can be erasable in Chomsky Normal Form");
        }

        self.is_start_symbol_erasable = true;
    }

    fn add_production(&mut self, lhs: impl TryInto<NonTerminal>, rhs: impl TryInto<CnfWord>) {
        let lhs = lhs.try_into().unwrap_or_else(|_| {
            panic!("Failed to convert to NonTerminal");
        });
        let rhs = rhs.try_into().unwrap_or_else(|_| {
            panic!("Failed to convert to CnfWord");
        });

        self.productions
            .entry(lhs)
            .or_insert_with(IndexSet::new)
            .insert(rhs);
    }
}

#[derive(Debug)]
pub struct CykTable {
    table: Vec<Vec<IndexSet<NonTerminal>>>,
    word: String,
    start_symbol: NonTerminal,
}

impl CykTable {
    pub fn new(size: usize, word: impl Into<String>, start_symbol: &NonTerminal) -> Self {
        CykTable {
            table: vec![vec![IndexSet::new(); size]; size],
            word: word.into(),
            start_symbol: start_symbol.clone(),
        }
    }

    pub fn contains(&self, i: usize, j: usize, value: &NonTerminal) -> bool {
        self.table[i][j].contains(value)
    }

    pub fn get(&self, i: usize, j: usize) -> &IndexSet<NonTerminal> {
        &self.table[i][j]
    }

    pub fn insert(&mut self, i: usize, j: usize, value: NonTerminal) {
        self.table[i][j].insert(value);
    }

    pub fn is_word_in_language(&self) -> bool {
        self.table[0][self.table.len() - 1].contains(&self.start_symbol)
    }
}

impl Display for CykTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "CYK Table for word \"{}\":\n", self.word)?;

        let mut builder = Builder::default();

        for (i, row) in self.table.iter().enumerate() {
            builder.push_record(row.iter().enumerate().map(|(j, s)| {
                if j >= i {
                    format!(
                        "V_{},{} = {}",
                        i + 1,
                        j + 1,
                        if s.is_empty() {
                            "∅".to_string()
                        } else {
                            format!("{{{}}}", s.iter().map(ToString::to_string).join(", "))
                        }
                    )
                } else {
                    String::new()
                }
            }));
        }

        builder.insert_record(0, (1..=self.table.len()).map(|j| format!("j = {}", j)));
        builder.insert_column(
            0,
            std::iter::once(String::new())
                .chain((1..=self.table.len()).map(|i| format!("i = {}", i))),
        );

        let mut table = builder.build();
        table.with(Style::rounded());

        writeln!(f, "{}", table)?;

        writeln!(
            f,
            "The word \"{}\" is {} in the language defined by the grammar, as the start symbol {} {} in the top-right cell.",
            self.word,
            if self.is_word_in_language() {
                "accepted"
            } else {
                "not accepted"
            },
            self.start_symbol,
            if self.is_word_in_language() {
                "is"
            } else {
                "is not"
            }
        )?;

        Ok(())
    }
}

impl ChomskyNormalFormGrammar {
    // pub fn to_context_free_grammar(&self) -> ContextFreeGrammar {
    //     let mut grammar = ContextFreeGrammar {
    //         start_symbol: self.start_symbol.clone(),
    //         erasing_productions: IndexSet::new(),
    //         productions: IndexMap::new(),
    //     };

    //     for (lhs, rhs) in &self.productions {
    //         let entry = grammar
    //             .productions
    //             .entry(lhs.clone())
    //             .or_insert_with(IndexSet::new);

    //         for word in rhs {
    //             match word {
    //                 CnfWord::Terminal(t) => {
    //                     entry.insert(Word(vec![ProductionSymbol::Terminal(t.clone())]));
    //                 }
    //                 CnfWord::NonTerminals(nt1, nt2) => {
    //                     entry.insert(Word(vec![
    //                         ProductionSymbol::NonTerminal(nt1.clone()),
    //                         ProductionSymbol::NonTerminal(nt2.clone()),
    //                     ]));
    //                 }
    //             }
    //         }
    //     }

    //     if self.is_start_symbol_erasable {
    //         grammar
    //             .erasing_productions
    //             .insert(self.start_symbol.clone());
    //     }

    //     grammar
    // }

    pub fn from_context_free_grammar(cfg: &ContextFreeGrammar) -> Self {
        let mut cfg = cfg.clone();
        cfg.eliminate_erasing_productions();
        cfg.eliminate_unit_productions();
        cfg.replace_terminals();

        let mut cnf = Self {
            is_start_symbol_erasable: cfg.erasing_productions.contains(&cfg.start_symbol),
            start_symbol: cfg.start_symbol,
            productions: IndexMap::new(),
        };

        let mut idx = 1;
        let mut new_productions = IndexMap::new();

        fn chomskify(
            word: Word<ProductionSymbol>,
            new_productions: &mut IndexMap<NonTerminal, IndexSet<CnfWord>>,
            idx: &mut i32,
        ) -> CnfWord {
            if word.0.len() == 1 {
                match &word.0[0] {
                    ProductionSymbol::NonTerminal(_) => {
                        panic!("Unit productions should have been eliminated")
                    }
                    ProductionSymbol::Terminal(t) => CnfWord::Terminal(t.clone()),
                }
            } else if word.0.len() == 2 {
                CnfWord::NonTerminals(
                    assert_non_terminal(&word.0[0]),
                    assert_non_terminal(&word.0[1]),
                )
            } else {
                let new_nt = NonTerminal(Symbol::new(format!("Y_{}", idx)));
                *idx += 1;

                let next_word = chomskify(Word(word.0[1..].to_vec()), new_productions, idx);

                new_productions
                    .entry(new_nt.clone())
                    .or_insert_with(IndexSet::new)
                    .insert(next_word);

                CnfWord::NonTerminals(assert_non_terminal(&word.0[0]), new_nt)
            }
        }

        fn assert_non_terminal(symbol: &ProductionSymbol) -> NonTerminal {
            match symbol {
                ProductionSymbol::Terminal(_) => {
                    panic!("Expected a non-terminal, but found a terminal")
                }
                ProductionSymbol::NonTerminal(nt) => nt.clone(),
            }
        }

        for (lhs, rhs) in cfg.productions {
            let entry = cnf.productions.entry(lhs).or_insert_with(IndexSet::new);

            for word in rhs {
                entry.insert(chomskify(word, &mut new_productions, &mut idx));
            }
        }

        cnf.productions.extend(new_productions);

        cnf
    }

    pub fn cyk(&self, word: &str) -> CykTable {
        let terminals = word
            .chars()
            .map(|c| Terminal(Symbol::new(c)))
            .collect::<Vec<_>>();

        let n = terminals.len();
        let mut table = CykTable::new(n, word, &self.start_symbol);

        for (lhs, rhs) in &self.productions {
            for word in rhs {
                if let CnfWord::Terminal(t) = word {
                    for (i, terminal) in terminals.iter().enumerate() {
                        if terminal == t {
                            table.insert(i, i, lhs.clone());
                        }
                    }
                }
            }
        }

        for d in 0..n - 1 {
            for i in 0..n - d - 1 {
                let j = i + d + 1;

                for k in i..j {
                    for (lhs, rhs) in &self.productions {
                        for word in rhs {
                            if let CnfWord::NonTerminals(nt1, nt2) = word {
                                if table.contains(i, k, nt1) && table.contains(k + 1, j, nt2) {
                                    table.insert(i, j, lhs.clone());
                                }
                            }
                        }
                    }
                }
            }
        }

        table
    }
}
