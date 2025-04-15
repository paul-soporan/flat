#[derive(Debug)]
pub struct Production {
    pub lhs: String,
    pub rhs: Vec<String>,
}

#[derive(Debug)]
pub struct Grammar {
    // pub terminals: Vec<String>,
    // pub non_terminals: Vec<String>,
    pub start_symbol: String,
    pub productions: Vec<Production>,
}
