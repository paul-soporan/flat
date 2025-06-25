use std::fmt::Display;

use derive_more::Display;

#[derive(Debug, Display, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Symbol(String);

impl Symbol {
    pub fn new(s: impl Into<String>) -> Self {
        let s = s.into();

        assert!(!s.is_empty());
        Symbol(s)
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

pub const EPSILON: &str = "ε";

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SymbolOrEpsilon {
    Epsilon,
    Symbol(Symbol),
}

impl Display for SymbolOrEpsilon {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SymbolOrEpsilon::Epsilon => write!(f, "{}", EPSILON),
            SymbolOrEpsilon::Symbol(symbol) => write!(f, "{}", symbol),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Word<S>(pub Vec<S>);

impl<S> Word<S> {
    pub fn new(symbols: impl IntoIterator<Item = S>) -> Self {
        Self(Vec::from_iter(symbols))
    }
}

impl<S: Display> Display for Word<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0.is_empty() {
            write!(f, "{}", EPSILON)
        } else {
            write!(
                f,
                "{}",
                self.0.iter().map(ToString::to_string).collect::<String>()
            )
        }
    }
}

impl<S> IntoIterator for Word<S> {
    type Item = S;
    type IntoIter = std::vec::IntoIter<S>;

    fn into_iter(self) -> std::vec::IntoIter<Self::Item> {
        self.0.into_iter()
    }
}

impl From<&str> for Word<Symbol> {
    fn from(s: &str) -> Self {
        Self(s.chars().map(Symbol::new).collect())
    }
}
