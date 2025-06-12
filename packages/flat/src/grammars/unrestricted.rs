use indexmap::{IndexMap, IndexSet};

use crate::grammars::types::{NonTerminal, ProductionSymbol, Word};

#[derive(Debug)]
pub struct UnrestrictedGrammar {
    start_symbol: NonTerminal,
    erasing_productions: IndexSet<Word<ProductionSymbol>>,
    productions: IndexMap<Word<ProductionSymbol>, IndexSet<Word<ProductionSymbol>>>,
}
