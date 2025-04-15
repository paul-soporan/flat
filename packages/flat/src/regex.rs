use crate::language::Symbol;

#[derive(Debug)]
pub enum RegularExpression {
    Zero,
    One,
    Symbol(Symbol),
    Union(Box<RegularExpression>, Box<RegularExpression>),
    Concatenation(Box<RegularExpression>, Box<RegularExpression>),
    KleeneStar(Box<RegularExpression>),
    Plus(Box<RegularExpression>),
}
