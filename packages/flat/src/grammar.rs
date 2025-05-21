use std::fmt::Display;

use derive_more::Display;
use indexmap::{indexset, IndexMap, IndexSet};
use itertools::Itertools;

use crate::language::Symbol;

#[derive(Debug, Display, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Terminal(Symbol);

#[derive(Debug, Display, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NonTerminal(Symbol);

#[derive(Debug, Display, Clone, PartialEq, Eq, Hash)]
pub enum ProductionSymbol {
    Terminal(Terminal),
    NonTerminal(NonTerminal),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Word<S: ToString>(pub Vec<S>);

impl<S: ToString> Display for Word<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.0.iter().map(|s| s.to_string()).collect::<String>()
        )
    }
}

pub trait Grammar {
    fn from_productions<S: AsRef<str>>(start_symbol: S, productions: &[impl AsRef<str>]) -> Self;
    fn to_unrestricted_grammar(&self) -> UnrestrictedGrammar;

    fn definition(&self) -> String {
        let grammar = self.to_unrestricted_grammar();

        let mut productions = IndexMap::with_capacity(grammar.productions.len());

        let mut words = IndexSet::new();

        for lhs in grammar.erasing_productions {
            productions
                .entry(lhs.to_string())
                .or_insert_with(Vec::new)
                .push("ε".to_owned());

            words.insert(lhs);
        }

        for (lhs, rhs) in grammar.productions {
            productions
                .entry(lhs.to_string())
                .or_insert_with(Vec::new)
                .extend(rhs.iter().map(|word| word.to_string()));

            words.insert(lhs);
            words.extend(rhs);
        }

        let mut non_terminals = IndexSet::from([grammar.start_symbol.clone()]);
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
            if a == &grammar.start_symbol {
                return std::cmp::Ordering::Less;
            }
            if b == &grammar.start_symbol {
                return std::cmp::Ordering::Greater;
            }
            a.cmp(b)
        });
        terminals.sort();

        productions.sort_by(|lhs1, _, lhs2, _| lhs1.cmp(lhs2));

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
            grammar.start_symbol
        );

        definition += "P = {\n";

        for (lhs, rhs) in productions {
            definition += &format!("  {} → {}\n", lhs, rhs.join(" | "));
        }

        definition += "}\n";

        definition
    }
}

#[derive(Debug)]
pub struct RightLinearGrammar {}

#[derive(Debug)]
pub struct LeftLinearGrammar {}

#[derive(Debug, Clone)]
pub struct ContextFreeGrammar {
    start_symbol: NonTerminal,
    erasing_productions: IndexSet<NonTerminal>,
    productions: IndexMap<NonTerminal, IndexSet<Word<ProductionSymbol>>>,
}

impl ContextFreeGrammar {
    pub fn eliminate_erasing_productions(&mut self) {
        let mut erasable_non_terminals = self.erasing_productions.clone();
        loop {
            let mut changed = false;

            'outer: for (lhs, rhs) in &self.productions {
                if erasable_non_terminals.contains(lhs) {
                    continue;
                }

                for word in rhs {
                    let is_lhs_erasable = word.0.iter().all(|symbol| {
                        if let ProductionSymbol::NonTerminal(nt) = symbol {
                            erasable_non_terminals.contains(nt)
                        } else {
                            false
                        }
                    });

                    if is_lhs_erasable {
                        erasable_non_terminals.insert(lhs.clone());

                        changed = true;
                        continue 'outer;
                    }
                }
            }

            if !changed {
                break;
            }
        }

        for rhs in self.productions.values_mut() {
            let mut next_productions = IndexSet::new();

            for word in rhs.iter() {
                let words = word
                    .0
                    .iter()
                    .cloned()
                    .map(|symbol| match &symbol {
                        ProductionSymbol::NonTerminal(nt) => {
                            if erasable_non_terminals.contains(nt) {
                                vec![Some(symbol), None]
                            } else {
                                vec![Some(symbol)]
                            }
                        }
                        ProductionSymbol::Terminal(_) => vec![Some(symbol)],
                    })
                    .multi_cartesian_product()
                    .filter_map(|word| {
                        let word = word.into_iter().flatten().collect::<Vec<_>>();
                        if word.is_empty() {
                            None
                        } else {
                            Some(Word(word))
                        }
                    });

                next_productions.extend(words);
            }

            *rhs = next_productions;
        }

        self.erasing_productions.clear();

        if erasable_non_terminals.contains(&self.start_symbol) {
            let new_start_symbol = NonTerminal(Symbol::new(format!("{}'", self.start_symbol)));

            self.erasing_productions.insert(new_start_symbol.clone());
            self.productions.insert(
                new_start_symbol.clone(),
                indexset! {Word(vec![ProductionSymbol::NonTerminal(
                    self.start_symbol.clone(),
                )])},
            );
            self.start_symbol = new_start_symbol;
        }
    }

    pub fn eliminate_unit_productions(&mut self) {
        let mut unit_closures = self
            .productions
            .keys()
            .map(|nt| {
                let mut unit_closure = IndexSet::new();
                let mut next_closure = IndexSet::from([nt.clone()]);

                loop {
                    unit_closure.extend(next_closure.clone());

                    let current_closure = next_closure;
                    next_closure = IndexSet::new();

                    for closure_nt in current_closure {
                        if let Some(rhs) = self.productions.get(&closure_nt) {
                            for word in rhs {
                                if word.0.len() == 1 {
                                    if let ProductionSymbol::NonTerminal(nt) = &word.0[0] {
                                        if !unit_closure.contains(nt) {
                                            next_closure.insert(nt.clone());
                                        }
                                    }
                                }
                            }
                        }
                    }

                    if next_closure.is_empty() {
                        break;
                    }
                }

                (nt.clone(), unit_closure)
            })
            .collect::<IndexMap<_, _>>();

        unit_closures.sort_by(|nt1, closure1, nt2, closure2| {
            closure1.len().cmp(&closure2.len()).then_with(|| {
                let one_contains_two = closure1.contains(nt2);
                let two_contains_one = closure2.contains(nt1);

                if one_contains_two && two_contains_one {
                    nt1.cmp(nt2)
                } else if one_contains_two {
                    std::cmp::Ordering::Greater
                } else if two_contains_one {
                    std::cmp::Ordering::Less
                } else {
                    nt1.cmp(nt2)
                }
            })
        });

        for (nt, _) in unit_closures {
            if let Some(rhs) = self.productions.get(&nt) {
                let new_productions = rhs
                    .iter()
                    .flat_map(|word| {
                        if word.0.len() == 1 {
                            if let ProductionSymbol::NonTerminal(child_nt) = &word.0[0] {
                                if let Some(child_rhs) = self.productions.get(child_nt) {
                                    let mut child_rhs = child_rhs.clone();
                                    child_rhs.retain(|word| {
                                        if word.0.len() == 1 {
                                            if let ProductionSymbol::NonTerminal(
                                                child_of_child_nt,
                                            ) = &word.0[0]
                                            {
                                                child_of_child_nt != &nt
                                            } else {
                                                true
                                            }
                                        } else {
                                            true
                                        }
                                    });

                                    return child_rhs;
                                } else {
                                    return IndexSet::new();
                                }
                            }
                        }

                        indexset! {word.clone()}
                    })
                    .collect::<IndexSet<_>>();

                self.productions.insert(nt, new_productions);
            }
        }
    }

    pub fn replace_terminals(&mut self) {
        let mut new_productions = IndexMap::new();

        for rhs in self.productions.values_mut() {
            *rhs = rhs
                .iter()
                .map(|word| {
                    if word.0.len() == 1 {
                        word.clone()
                    } else {
                        Word(
                            word.0
                                .iter()
                                .map(|symbol| match symbol {
                                    ProductionSymbol::Terminal(t) => {
                                        let nt = NonTerminal(Symbol::new(format!("X_{}", t)));
                                        new_productions
                                            .entry(nt.clone())
                                            .or_insert_with(IndexSet::new)
                                            .insert(Word(vec![symbol.clone()]));

                                        ProductionSymbol::NonTerminal(nt)
                                    }
                                    ProductionSymbol::NonTerminal(_) => symbol.clone(),
                                })
                                .collect(),
                        )
                    }
                })
                .collect::<IndexSet<_>>();
        }

        self.productions.extend(new_productions);
    }

    pub fn to_chomsky_normal_form(&self) -> ChomskyNormalFormGrammar {
        let mut cfg = self.clone();
        cfg.eliminate_erasing_productions();
        cfg.eliminate_unit_productions();
        cfg.replace_terminals();

        let mut cnf_grammar = ChomskyNormalFormGrammar {
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
            let entry = cnf_grammar
                .productions
                .entry(lhs)
                .or_insert_with(IndexSet::new);

            for word in rhs {
                entry.insert(chomskify(word, &mut new_productions, &mut idx));
            }
        }

        cnf_grammar.productions.extend(new_productions);

        cnf_grammar
    }
}

impl Grammar for ContextFreeGrammar {
    fn from_productions<S: AsRef<str>>(start_symbol: S, productions: &[impl AsRef<str>]) -> Self {
        let start_symbol = NonTerminal(Symbol::new(start_symbol.as_ref()));
        let mut grammar = Self {
            start_symbol,
            erasing_productions: IndexSet::new(),
            productions: IndexMap::new(),
        };

        for production in productions {
            let parts = production
                .as_ref()
                .split("→")
                .map(|part| part.trim())
                .collect::<Vec<_>>();
            if parts.len() != 2 {
                panic!("Invalid production format");
            }

            let lhs = NonTerminal(Symbol::new(parts[0]));
            parts[1].split("|").for_each(|rhs| {
                let rhs = rhs.trim();
                if rhs == "ε" {
                    grammar.erasing_productions.insert(lhs.clone());
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
                    grammar
                        .productions
                        .entry(lhs.clone())
                        .or_insert_with(IndexSet::new)
                        .insert(word);
                }
            })
        }

        grammar
    }

    fn to_unrestricted_grammar(&self) -> UnrestrictedGrammar {
        UnrestrictedGrammar {
            start_symbol: self.start_symbol.clone(),
            erasing_productions: self
                .erasing_productions
                .iter()
                .map(|k| Word(vec![ProductionSymbol::NonTerminal(k.clone())]))
                .collect(),
            productions: self
                .productions
                .iter()
                .map(|(k, v)| {
                    (
                        Word(vec![ProductionSymbol::NonTerminal(k.clone())]),
                        v.clone(),
                    )
                })
                .collect(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CnfWord {
    Terminal(Terminal),
    NonTerminals(NonTerminal, NonTerminal),
}

#[derive(Debug, Clone)]
pub struct ChomskyNormalFormGrammar {
    start_symbol: NonTerminal,
    is_start_symbol_erasable: bool,
    productions: IndexMap<NonTerminal, IndexSet<CnfWord>>,
}

impl ChomskyNormalFormGrammar {
    pub fn to_context_free_grammar(&self) -> ContextFreeGrammar {
        let mut grammar = ContextFreeGrammar {
            start_symbol: self.start_symbol.clone(),
            erasing_productions: IndexSet::new(),
            productions: IndexMap::new(),
        };

        for (lhs, rhs) in &self.productions {
            let entry = grammar
                .productions
                .entry(lhs.clone())
                .or_insert_with(IndexSet::new);

            for word in rhs {
                match word {
                    CnfWord::Terminal(t) => {
                        entry.insert(Word(vec![ProductionSymbol::Terminal(t.clone())]));
                    }
                    CnfWord::NonTerminals(nt1, nt2) => {
                        entry.insert(Word(vec![
                            ProductionSymbol::NonTerminal(nt1.clone()),
                            ProductionSymbol::NonTerminal(nt2.clone()),
                        ]));
                    }
                }
            }
        }

        if self.is_start_symbol_erasable {
            grammar
                .erasing_productions
                .insert(self.start_symbol.clone());
        }

        grammar
    }

    pub fn to_greibach_normal_form(&self) -> GreibachNormalFormGrammar {
        let non_terminals = self
            .productions
            .keys()
            .cloned()
            .enumerate()
            .map(|(i, nt)| (nt, NonTerminal(Symbol::new(format!("A_{}", i + 1)))))
            .collect::<IndexMap<_, _>>();

        let mut cfg = ContextFreeGrammar {
            start_symbol: non_terminals[&self.start_symbol].clone(),
            erasing_productions: if self.is_start_symbol_erasable {
                indexset! {non_terminals[&self.start_symbol].clone()}
            } else {
                IndexSet::new()
            },
            productions: self
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

        let mut gnf = GreibachNormalFormGrammar {
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
                            |(terminal, non_terminals)| {
                                let mut non_terminals = non_terminals.clone();
                                non_terminals.extend(word.0[1..].iter().map(|nt| match nt {
                                    ProductionSymbol::NonTerminal(nt) => nt.clone(),
                                    _ => panic!("Expected a non-terminal"),
                                }));

                                (terminal.clone(), non_terminals)
                            },
                        ));
                    } else {
                        let mut word = word.clone();
                        let non_terminals = word.0.split_off(1);

                        next_rhs.insert((
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
                            |(terminal, non_terminals)| {
                                let mut non_terminals = non_terminals.clone();
                                non_terminals.extend(word.0[1..].iter().map(|nt| match nt {
                                    ProductionSymbol::NonTerminal(nt) => nt.clone(),
                                    _ => panic!("Expected a non-terminal"),
                                }));

                                (terminal.clone(), non_terminals)
                            },
                        ));
                    } else {
                        let mut word = word.clone();
                        let non_terminals = word.0.split_off(1);

                        next_rhs.insert((
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
}

impl Grammar for ChomskyNormalFormGrammar {
    fn from_productions<S: AsRef<str>>(start_symbol: S, productions: &[impl AsRef<str>]) -> Self {
        unimplemented!()
    }

    fn to_unrestricted_grammar(&self) -> UnrestrictedGrammar {
        self.to_context_free_grammar().to_unrestricted_grammar()
    }
}

type GnfWord = (Terminal, Vec<NonTerminal>);

#[derive(Debug)]
pub struct GreibachNormalFormGrammar {
    start_symbol: NonTerminal,
    is_start_symbol_erasable: bool,
    productions: IndexMap<NonTerminal, IndexSet<GnfWord>>,
}

impl GreibachNormalFormGrammar {
    pub fn to_context_free_grammar(&self) -> ContextFreeGrammar {
        let mut cfg = ContextFreeGrammar {
            start_symbol: self.start_symbol.clone(),
            erasing_productions: if self.is_start_symbol_erasable {
                indexset! {self.start_symbol.clone()}
            } else {
                IndexSet::new()
            },
            productions: IndexMap::new(),
        };

        for (lhs, rhs) in &self.productions {
            let entry = cfg
                .productions
                .entry(lhs.clone())
                .or_insert_with(IndexSet::new);

            for (terminal, non_terminals) in rhs {
                entry.insert(Word(
                    std::iter::once(ProductionSymbol::Terminal(terminal.clone()))
                        .chain(
                            non_terminals
                                .iter()
                                .cloned()
                                .map(|nt| ProductionSymbol::NonTerminal(nt)),
                        )
                        .collect(),
                ));
            }
        }

        cfg
    }
}

impl Grammar for GreibachNormalFormGrammar {
    fn from_productions<S: AsRef<str>>(start_symbol: S, productions: &[impl AsRef<str>]) -> Self {
        unimplemented!()
    }

    fn to_unrestricted_grammar(&self) -> UnrestrictedGrammar {
        self.to_context_free_grammar().to_unrestricted_grammar()
    }
}

#[derive(Debug)]
pub struct UnrestrictedGrammar {
    start_symbol: NonTerminal,
    erasing_productions: IndexSet<Word<ProductionSymbol>>,
    productions: IndexMap<Word<ProductionSymbol>, IndexSet<Word<ProductionSymbol>>>,
}
