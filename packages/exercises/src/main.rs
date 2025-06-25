use flat::{
    automata::{
        finite_state::{Dfa, EpsilonNfa, Nfa},
        pushdown::{AcceptanceCondition, PushdownAutomaton},
        turing_machine::TuringMachine,
    },
    grammars::{
        chomsky_normal_form::ChomskyNormalFormGrammar, context_free::ContextFreeGrammar,
        greibach_normal_form::GreibachNormalFormGrammar, types::Grammar,
    },
    language::{Symbol, Word},
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

    let dfa = Dfa::from(&nfa);
    println!("DFA:\n{}", dfa.transition_table());
    println!("DFA Definition:\n{}", dfa.definition());

    let (r1, intermediary_regexes) = RegularExpression::from_dfa(&dfa);

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

    let enfa = EpsilonNfa::from(&r);

    println!("Epsilon NFA:\n{}", enfa.transition_table());
    println!("Epsilon NFA Definition:\n{}", enfa.definition());

    let mut nfa = Nfa::from(&enfa);
    println!("NFA:\n{}", nfa.transition_table());

    nfa.remove_unreachable_states();

    println!("Simpler NFA:\n{}", nfa.transition_table());
    println!("Simpler NFA Definition:\n{}", nfa.definition());

    let dfa = Dfa::from(&nfa);
    println!("DFA:\n{}", dfa.transition_table());
    println!("DFA Definition:\n{}", dfa.definition());

    let (r1, intermediary_regexes) = RegularExpression::from_dfa(&dfa);

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
    let cnf = ChomskyNormalFormGrammar::from_productions(
        "S",
        &[
            "S → TT | AC",
            "T → AC | DA | AB | BA",
            "C → XB",
            "D → BX",
            "X → TT | AB | BA",
            "A → a",
            "B → b",
        ],
    );

    let table = cnf.cyk("baabab");
    println!("{}", table);
}

fn turing_machine_session_example_1() {
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

    let input = Word::from("00111");

    let run = tm.run(&input);
    println!("{}", run);
}

fn turing_machine_session_example_2() {
    let tm = TuringMachine::from_definition(
        "q1",
        &["qa"],
        &[
            ("q1", "0", "B", 1, "q2"),
            ("q2", "X", "X", 1, "q2"),
            ("q2", "0", "X", 1, "q3"),
            ("q2", "B", "B", 1, "qa"),
            ("q3", "X", "X", 1, "q3"),
            ("q3", "0", "0", 1, "q4"),
            ("q4", "X", "X", 1, "q4"),
            ("q4", "0", "X", 1, "q3"),
            ("q3", "B", "B", -1, "q5"),
            ("q5", "X", "X", -1, "q5"),
            ("q5", "0", "0", -1, "q5"),
            ("q5", "B", "B", 1, "q2"),
        ],
    );

    let input = Word::from("000");

    let run = tm.run(&input);
    println!("{}", run);
}

fn pda() {
    // let mut pda = PushdownAutomaton::from_definition(
    //     "q0",
    //     "⊥",
    //     &[],
    //     &[
    //         ("q0", "a", "⊥", &[(&["a", "⊥"], "q0")]),
    //         ("q0", "a", "a", &[(&["a", "a"], "q0")]),
    //         ("q0", "b", "a", &[(&[], "q1")]),
    //         ("q1", "b", "a", &[(&[], "q1")]),
    //         ("q1", "ε", "⊥", &[(&[], "q2")]),
    //     ],
    //     AcceptanceCondition::EmptyStack.into(),
    // );

    let mut pda = PushdownAutomaton::from_definition(
        "q0",
        "⊥",
        &["q2"],
        &[
            ("q0", "a", "⊥", &[(&["a", "⊥"], "q0")]),
            ("q0", "a", "a", &[(&["a", "a"], "q0")]),
            ("q0", "b", "a", &[(&[], "q1")]),
            ("q1", "b", "a", &[(&[], "q1")]),
            ("q1", "ε", "⊥", &[(&["⊥"], "q2")]),
        ],
        AcceptanceCondition::FinalState.into(),
    );

    pda.accept_by_empty_stack();

    let input = Word::from("aabb");

    let run = pda.run(&input);
    println!("{}", run);
}

fn cfg_to_pda_session_example_1() {
    let cfg = ContextFreeGrammar::from_productions(
        "S",
        &["S → S_1 | S_2", "S_1 → ε | aS_1b", "S_2 → a | bbS_2c"],
    );
    let pda = PushdownAutomaton::from(&cfg);

    println!("PDA from CFG:\n");
    for (from_state, symbol, popped_stack_symbol, pushed_stack_symbols, to_state) in
        pda.transitions()
    {
        println!(
            "{} --{},{}/{}--> {}",
            from_state, symbol, popped_stack_symbol, pushed_stack_symbols, to_state
        );
    }
}

fn gnf_to_pda_session_example_1() {
    let gnf = GreibachNormalFormGrammar::from_productions(
        "S",
        &["S → ε | aXZ", "X → bXX | bZ", "Z → a | cZ"],
    );
    let pda = PushdownAutomaton::from(&gnf);

    println!("PDA from GNF:\n");
    for (from_state, symbol, popped_stack_symbol, pushed_stack_symbols, to_state) in
        pda.transitions()
    {
        println!(
            "{} --{},{}/{}--> {}",
            from_state, symbol, popped_stack_symbol, pushed_stack_symbols, to_state
        );
    }
}

fn pda_session_example_2() {
    let mut pda = PushdownAutomaton::from_definition(
        "q0",
        "⊥",
        &["q4"],
        &[
            ("q0", "a", "⊥", &[(&["a", "⊥"], "q0")]),
            ("q0", "a", "a", &[(&["a", "a"], "q0")]),
            ("q0", "b", "a", &[(&["b", "a"], "q1")]),
            ("q1", "b", "b", &[(&["b", "b"], "q1")]),
            ("q1", "c", "b", &[(&[], "q2")]),
            ("q2", "c", "b", &[(&[], "q2")]),
            ("q2", "d", "a", &[(&[], "q3")]),
            ("q3", "d", "a", &[(&[], "q3")]),
            ("q3", "ε", "⊥", &[(&["⊥"], "q4")]),
        ],
        AcceptanceCondition::FinalState.into(),
    );

    let input = Word::from("abbccd");

    let run = pda.run(&input);
    println!("{}", run);
}

fn cyk_session_example_2() {
    let cnf = ChomskyNormalFormGrammar::from_productions(
        "S",
        &[
            "S → ε | c | ZZ | XY | YX",
            "Z → c | ZZ | XY | YX",
            "X → a | ZA",
            "Y → b | ZB",
            "A → a",
            "B → b",
        ],
    );

    let table = cnf.cyk("aacbb");
    println!("{}", table);
}

fn cyk_exam() {
    let cnf = ChomskyNormalFormGrammar::from_productions(
        "S",
        &[
            "S → AR | AT | BU",
            "R → XY",
            "T → YX",
            "U → XX",
            "A → a",
            "B → b",
            "X → SA | a",
            "Y → SB | b",
        ],
    );

    let table = cnf.cyk("abaaab");
    println!("{}", table);
}

fn turing_machine_exam() {
    let tm = TuringMachine::from_definition(
        "q0",
        &["qf"],
        &[
            ("q0", "0", "0", 1, "q0"),
            ("q0", "1", "1", 1, "q0"),
            ("q0", "B", "B", -1, "q1"),
            ("q1", "1", "0", -1, "q1"),
            ("q1", "0", "1", 1, "qf"),
            ("q1", "B", "B", -1, "qf"),
        ],
    );

    let input = Word::from("100");

    let run = tm.run(&input);
    println!("{}", run);
}

fn greiback_to_pda_exam() {
    let gnf = GreibachNormalFormGrammar::from_productions(
        "S",
        &[
            "S → ε | cS | aSBS | bSAS | aSBSC | bSASC",
            "A → a",
            "B → b",
            "C → c",
        ],
    );
    let pda = PushdownAutomaton::from(&gnf);

    println!("PDA from GNF:\n");
    for (from_state, symbol, popped_stack_symbol, pushed_stack_symbols, to_state) in
        pda.transitions()
    {
        println!(
            "{} --{},{}/{}--> {}\n",
            from_state, symbol, popped_stack_symbol, pushed_stack_symbols, to_state
        );
    }

    let input = Word::from("caaccbb");

    let run = pda.run(&input);
    println!("{}", run);
}

fn main() {
    // cyk_exam();
    // turing_machine_exam();
    greiback_to_pda_exam();

    // regex_to_dfa();
    // nfa_to_regex();
    // grammars();
    // pda();

    // cfg_to_pda_session_example_1();
    // gnf_to_pda_session_example_1();

    // cyk_session_example_2();
    // pda_session_example_2();

    // turing_machine_session_example_1();
    // turing_machine_session_example_2();
}
