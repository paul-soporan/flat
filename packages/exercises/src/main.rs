use flat::{
    automata::{
        finite_state::{Dfa, EpsilonNfa, Nfa},
        turing_machine::TuringMachine,
    },
    grammars::{
        chomsky_normal_form::ChomskyNormalFormGrammar,
        context_free::ContextFreeGrammar,
        greibach_normal_form::GreibachNormalFormGrammar,
        types::{Grammar, Word},
    },
    language::Symbol,
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
    let r = "(a^*b)^* + (a + b)^*".parse::<RegularExpression>().unwrap();
    // let r = RegularExpression::try_from("(a + bc^*)^*").unwrap();

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

    let cnf = ChomskyNormalFormGrammar::from_context_free_grammar(&cfg);
    println!("Chomsky Normal Form:\n{}", cnf.definition());

    let gnf = GreibachNormalFormGrammar::from_chomsky_normal_form(&cnf);
    println!("Greibach Normal Form:\n{}", gnf.definition());
}

fn cyk() {
    // let cfg = ContextFreeGrammar::from_productions(
    //     "S",
    //     &[
    //         "S → TT | AC",
    //         "T → AC | DA | AB | BA",
    //         "C → XB",
    //         "D → BX",
    //         "X → TT | AB | BA",
    //         "A → a",
    //         "B → b",
    //     ],
    // );

    // let cnf = cfg.to_chomsky_normal_form();

    // let table = cnf.cyk("baabab");
    // println!("{}", table);
}

fn turing_machine() {
    let tm = TuringMachine::from_definition(
        "q0",
        &["q4"],
        &[
            ("q0", "0", "X", 1, "q1"),
            ("q0", "Y", "Y", 1, "q3"),
            ("q1", "0", "0", 1, "q1"),
            ("q1", "Y", "Y", 1, "q1"),
            ("q1", "1", "Y", -1, "q2"),
            ("q2", "0", "0", -1, "q2"),
            ("q2", "Y", "Y", -1, "q2"),
            ("q2", "X", "X", 1, "q0"),
            ("q3", "Y", "Y", 1, "q3"),
            ("q3", "B", "B", 1, "q4"),
        ],
    );

    let input = Word(vec![
        Symbol::new("0".to_string()),
        Symbol::new("0".to_string()),
        Symbol::new("1".to_string()),
        Symbol::new("1".to_string()),
    ]);

    let is_accepted = tm.run(&input);
    println!("Input: {}", input);
    println!("Accepted: {}", is_accepted);
}

fn main() {
    // regex_to_dfa();
    // nfa_to_regex();
    // grammars();
    // cyk();
    turing_machine();
}
