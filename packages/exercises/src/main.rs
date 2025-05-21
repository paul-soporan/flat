use flat::{
    automata::{Dfa, EpsilonNfa, Nfa},
    grammar::{ContextFreeGrammar, Grammar},
    regex::RegularExpression,
};

fn nfa_to_regex() {
    let nfa = Nfa::from_definition(
        "q0",
        &["q2"],
        &[
            ("q0", "a", &["q1"]),
            ("q0", "b", &["q0"]),
            ("q1", "a", &["q2"]),
            ("q1", "b", &["q0"]),
            ("q2", "a", &["q2"]),
            ("q2", "b", &["q2"]),
        ],
    );
    println!("NFA:\n{}", nfa.transition_table());
    println!("NFA Definition:\n{}", nfa.definition());

    let dfa = Dfa::from(nfa);
    println!("DFA:\n{}", dfa.transition_table());
    println!("DFA Definition:\n{}", dfa.definition());

    let (r1, intermediary_regexes) = RegularExpression::from_dfa(dfa);

    println!("Regular Expression from DFA:\n{}", r1.to_string());

    println!("Intermediary Regular Expressions:");
    for ((i, j, k), regex) in intermediary_regexes.iter() {
        println!("  R{},{},{}: {}", i, j, k, regex.to_string());
    }
}

fn regex_to_dfa() {
    let r = RegularExpression::try_from("(a^*b)^* + (a + b)^*").unwrap();

    println!("Regular Expression:\n{}", r.to_string());

    let enfa = EpsilonNfa::from(r);

    println!("Epsilon NFA:\n{}", enfa.transition_table());
    println!("Epsilon NFA Definition:\n{}", enfa.definition());

    let mut nfa = Nfa::from(enfa);
    println!("NFA:\n{}", nfa.transition_table());

    nfa.remove_unreachable_states();

    println!("Simpler NFA:\n{}", nfa.transition_table());
    println!("Simpler NFA Definition:\n{}", nfa.definition());

    let dfa = Dfa::from(nfa);
    println!("DFA:\n{}", dfa.transition_table());
    println!("DFA Definition:\n{}", dfa.definition());

    let (r1, intermediary_regexes) = RegularExpression::from_dfa(dfa);

    println!("Regular Expression from DFA:\n{}", r1.to_string());

    println!("Intermediary Regular Expressions:");
    for ((i, j, k), regex) in intermediary_regexes.iter() {
        println!("  R{},{},{}: {}", i, j, k, regex.to_string());
    }
}

fn grammars() {
    // let cfg = ContextFreeGrammar::from_productions(
    //     "S",
    //     &["S → Aa | B | c", "A → a | Bca | B", "B → ε | A | bb"],
    // );

    let cfg =
        ContextFreeGrammar::from_productions("S", &["S → XA | BB", "B → b | SB", "X → b", "A → a"]);

    let cnf = cfg.to_chomsky_normal_form();
    println!("Chomsky Normal Form:\n{}", cnf.definition());

    let gnf = cnf.to_greibach_normal_form();
    println!("Greibach Normal Form:\n{}", gnf.definition());
}

fn main() {
    // regex_to_dfa();
    // nfa_to_regex();
    grammars();
}
