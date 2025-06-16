use std::borrow::Cow;

use indexmap::{indexset, IndexMap, IndexSet};
use itertools::Itertools;

use crate::{
    grammars::types::{Grammar, NonTerminal, ProductionSymbol},
    language::{Symbol, Word},
};

#[derive(Debug, Clone)]
pub struct ContextFreeGrammar {
    pub(super) start_symbol: NonTerminal,
    pub(super) erasing_productions: IndexSet<NonTerminal>,
    pub(super) productions: IndexMap<NonTerminal, IndexSet<Word<ProductionSymbol>>>,
}

impl Grammar<NonTerminal, Word<ProductionSymbol>> for ContextFreeGrammar {
    fn new(start_symbol: NonTerminal) -> Self {
        Self {
            start_symbol,
            erasing_productions: IndexSet::new(),
            productions: IndexMap::new(),
        }
    }

    fn start_symbol(&self) -> &NonTerminal {
        &self.start_symbol
    }

    fn erasing_productions(&self) -> Cow<'_, IndexSet<NonTerminal>> {
        Cow::Borrowed(&self.erasing_productions)
    }

    fn productions(&self) -> &IndexMap<NonTerminal, IndexSet<Word<ProductionSymbol>>> {
        &self.productions
    }

    fn add_erasing_production(&mut self, lhs: impl TryInto<NonTerminal>) {
        let lhs = lhs.try_into().unwrap_or_else(|_| {
            panic!("Failed to convert to NonTerminal");
        });

        self.erasing_productions.insert(lhs);
    }

    fn add_production(
        &mut self,
        lhs: impl TryInto<NonTerminal>,
        rhs: impl TryInto<Word<ProductionSymbol>>,
    ) {
        let lhs = lhs.try_into().unwrap_or_else(|_| {
            panic!("Failed to convert to NonTerminal");
        });
        let rhs = rhs.try_into().unwrap_or_else(|_| {
            panic!("Failed to convert to Word<ProductionSymbol>");
        });

        self.productions
            .entry(lhs)
            .or_insert_with(IndexSet::new)
            .insert(rhs);
    }
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
                            Some(Word::new(word))
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
                indexset! {Word::new(vec![ProductionSymbol::NonTerminal(
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
                        Word::new(word.0.iter().map(|symbol| match symbol {
                            ProductionSymbol::Terminal(t) => {
                                let nt = NonTerminal(Symbol::new(format!("X_{}", t)));
                                new_productions
                                    .entry(nt.clone())
                                    .or_insert_with(IndexSet::new)
                                    .insert(Word::new(vec![symbol.clone()]));

                                ProductionSymbol::NonTerminal(nt)
                            }
                            ProductionSymbol::NonTerminal(_) => symbol.clone(),
                        }))
                    }
                })
                .collect::<IndexSet<_>>();
        }

        self.productions.extend(new_productions);
    }
}
