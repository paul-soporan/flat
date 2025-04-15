use flat::{
    automata::{EpsilonNfa, Nfa},
    language::Symbol,
    regex::RegularExpression,
};

fn main() {
    let r = RegularExpression::Union(
        RegularExpression::Concatenation(
            RegularExpression::Symbol(Symbol::new("a".to_string())).into(),
            RegularExpression::KleeneStar(
                RegularExpression::Symbol(Symbol::new("c".to_string())).into(),
            )
            .into(),
        )
        .into(),
        RegularExpression::Symbol(Symbol::new("b".to_string())).into(),
    );

    let enfa = EpsilonNfa::from(r);
    dbg!(&enfa);
    println!("Epsilon NFA:\n{}", enfa.transition_table());

    let mut nfa = Nfa::from(enfa);
    println!("NFA:\n{}", nfa.transition_table());

    nfa.remove_unreachable_states();

    println!("Simpler NFA:\n{}", nfa.transition_table());
}
