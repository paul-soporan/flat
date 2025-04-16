use indexmap::IndexMap;

use crate::language::{Symbol, Word};

#[derive(Debug)]
pub struct Grammar {
    // pub terminals: Vec<String>,
    // pub non_terminals: Vec<String>,
    pub start_symbol: Symbol,
    pub productions: IndexMap<Vec<Symbol>, Vec<Word>>,
}
