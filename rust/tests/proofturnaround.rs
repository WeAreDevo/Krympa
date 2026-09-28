use krympa::proof_turnaround::_count_nontrivial_steps;
use krympa::proof_turnaround::_debug_print_parsed_proof;
use krympa::proof_turnaround::eq_proof_procedure;
use krympa::proof_turnaround::parse_vampire_proof;
use krympa::proof_turnaround::turn_proof_around;
use krympa::proof_turnaround::Formula;
use krympa::proof_turnaround::SuperpositionStep;

#[test]
fn eliminates_turned_equality_resolution_and_reflexive_eq() {
    let proof_text = r#"
1. g(X) = f(X) [input]
2. g(g(b)) != f(f(b)) [negated conjecture]
3. g(f(b)) != f(f(b)) [superposition 1,2]
4. f(f(b)) != f(f(b)) [superposition 1,3]
5. $false [equality resolution 4]
"#;

    let parsed = parse_vampire_proof(proof_text);

    // we expect the “useful” turned proof to have 3 nontrivial steps:
    // 1) axiom
    // 2) g(f(b)) = f(f(b))  (contraposed from step 3, using implicit f(f(b))=f(f(b)))
    // 3) g(g(b)) = f(f(b))  (contraposed from step 2)

    let steps = turn_proof_around(&parsed);
    assert_eq!(_count_nontrivial_steps(&steps), 4);

    // check that the key equalities appear somewhere in the result
    // (qe don't rely on exact indices because the turnaround rethreads indices)
    let strs: Vec<String> = steps.values().map(|s| s.formula.to_string()).collect();

    assert!(strs.iter().any(|s| s.contains("g(X) = f(X)")));
    assert!(strs.iter().any(|s| s.contains("g(f(b)) = f(f(b))")));
    assert!(strs.iter().any(|s| s.contains("g(g(b)) = f(f(b))")));

    // also ensure we didn't keep a visible reflexive equality as a step
    assert!(!strs.iter().any(|s| s.trim() == "f(f(b)) = f(f(b))"));
}

#[test]
fn proof_turnaround() {
    let proof_text = r#"
% Running in auto input_syntax mode. Trying TPTP
% Refutation found. Thanks to Tanya!
% SZS status Theorem for Equation2892_implies_Equation2680
% SZS output start Proof for Equation2892_implies_Equation2680
1. ! [X0,X1,X2] : op(op(op(X0,op(X1,X2)),X2),X2) = X0 [input]
2. ! [X0,X1,X2] : op(op(op(X0,X1),op(X2,X0)),X1) = X0 [input]
3. ~! [X0,X1,X2] : op(op(op(X0,X1),op(X2,X0)),X1) = X0 [negated conjecture 2]
4. ? [X0,X1,X2] : op(op(op(X0,X1),op(X2,X0)),X1) != X0 [ennf transformation 3]
5. ? [X0,X1,X2] : op(op(op(X0,X1),op(X2,X0)),X1) != X0 => sK0 != op(op(op(sK0,sK1),op(sK2,sK0)),sK1) [choice axiom]
6. sK0 != op(op(op(sK0,sK1),op(sK2,sK0)),sK1) [skolemisation 4,5]
7. op(op(op(X0,op(X1,X2)),X2),X2) = X0 [cnf transformation 1]
8. sK0 != op(op(op(sK0,sK1),op(sK2,sK0)),sK1) [cnf transformation 6]
9. op(op(op(X3,X0),X2),X2) = X3 [superposition 7,7]
13. op(X0,op(X1,X2)) = op(X0,X2) [superposition 9,7]
14. op(X3,X4) = op(X3,X5) [superposition 9,9]
20. sK0 != op(op(op(sK0,sK1),sK0),sK1) [backward demodulation 8,13]
21. op(op(op(X0,X1),X2),X3) = X0 [superposition 14,9]
30. sK0 != op(op(op(sK0,sK1),X12),sK1) [superposition 20,14]
39. $false [subsumption resolution 30,21]
% SZS output end Proof for Equation2892_implies_Equation2680
% ------------------------------
% Version: Vampire 4.8 (commit )
% Termination reason: Refutation

% Memory used [KB]: 4989
% Time elapsed: 0.0000 s
% ------------------------------
% ------------------------------
"#;

    let steps_map = parse_vampire_proof(proof_text);
    _debug_print_parsed_proof(&steps_map);
    let final_proof = eq_proof_procedure(proof_text);
    println!("\n[TEST] Final proof");
    println!("{}", final_proof);
}

// Proof of big_step_lemma_0023: ends with $false [trivial inequality removal 2903].
// After turnaround, the step that was $false should hold the conjecture formula
// with non-empty deps. Regression for the bug where drop_trivial_deps was dropping
// deps without propagating them, leaving the conclusion step with no dep chain.
const BIG_STEP_0023_PROOF: &str = r#"1. ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0 [input(axiom)]
2. ! [X0,X1,X2,X3,X4] : op(X3,op(X0,X3)) = op(op(X3,op(X0,X3)),op(X4,op(op(X0,op(op(X1,op(op(X2,X0),X1)),X0)),X4))) [input(conjecture)]
3. ~! [X0,X1,X2,X3,X4] : op(X3,op(X0,X3)) = op(op(X3,op(X0,X3)),op(X4,op(op(X0,op(op(X1,op(op(X2,X0),X1)),X0)),X4))) [negated conjecture 2]
4. ? [X0,X1,X2,X3,X4] : op(X3,op(X0,X3)) != op(op(X3,op(X0,X3)),op(X4,op(op(X0,op(op(X1,op(op(X2,X0),X1)),X0)),X4))) [ennf transformation 3]
5. ? [X0,X1,X2,X3,X4] : op(X3,op(X0,X3)) != op(op(X3,op(X0,X3)),op(X4,op(op(X0,op(op(X1,op(op(X2,X0),X1)),X0)),X4))) => op(sK3,op(sK0,sK3)) != op(op(sK3,op(sK0,sK3)),op(sK4,op(op(sK0,op(op(sK1,op(op(sK2,sK0),sK1)),sK0)),sK4))) [skolem symbol introduction]
6. op(sK3,op(sK0,sK3)) != op(op(sK3,op(sK0,sK3)),op(sK4,op(op(sK0,op(op(sK1,op(op(sK2,sK0),sK1)),sK0)),sK4))) [skolemisation 4,5]
7. op(X0,op(X1,op(op(X2,X0),X1))) = X0 [cnf transformation 1]
8. op(sK3,op(sK0,sK3)) != op(op(sK3,op(sK0,sK3)),op(sK4,op(op(sK0,op(op(sK1,op(op(sK2,sK0),sK1)),sK0)),sK4))) [cnf transformation 6]
9. op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3))) [superposition 7,7]
10. op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1 [superposition 7,7]
34. op(X2,X3) = op(op(X2,X3),op(op(X4,op(op(X0,op(op(X1,X2),X0)),X4)),op(X3,op(X2,X3)))) [superposition 10,9]
35. op(X3,op(X2,X3)) = op(op(X3,op(X2,X3)),op(op(X4,op(op(X5,op(X0,op(op(X1,X2),X0))),X4)),op(X0,op(op(X1,X2),X0)))) [superposition 10,9]
2171. op(X3,op(X0,X3)) = op(op(X3,op(X0,X3)),op(op(X4,op(op(X0,op(op(X1,op(op(X2,X0),X1)),X0)),X4)),op(op(X0,op(op(X1,op(op(X2,X0),X1)),X0)),op(op(op(X1,op(op(X2,X0),X1)),X0),op(X0,op(op(X1,op(op(X2,X0),X1)),X0)))))) [superposition 35,34]
2333. op(X3,op(X0,X3)) = op(op(X3,op(X0,X3)),op(X4,op(op(X0,op(op(X1,op(op(X2,X0),X1)),X0)),X4))) [forward demodulation 2171,9]
2903. op(sK3,op(sK0,sK3)) != op(sK3,op(sK0,sK3)) [superposition 8,2333]
3049. $false [trivial inequality removal 2903]"#;

#[test]
fn test_turnaround_preserves_deps_through_trivial_step() {
    let parsed = parse_vampire_proof(BIG_STEP_0023_PROOF);
    let result = turn_proof_around(&parsed);

    let step_3049 = result
        .get(&3049)
        .expect("step 3049 missing from turned-around proof");

    assert!(
        matches!(&step_3049.formula, Formula::Forall(_, inner) if matches!(inner.as_ref(), Formula::Eq(_, _))),
        "step 3049 should be a universally-quantified equality after turnaround; got: {}",
        step_3049.formula
    );

    assert!(
        !step_3049.deps.is_empty(),
        "step 3049 has no deps after turnaround — drop_trivial_deps is losing the chain (regression)"
    );
}

#[test]
fn test_turnaround_output_contains_superposition_steps() {
    let parsed = parse_vampire_proof(BIG_STEP_0023_PROOF);
    let result = turn_proof_around(&parsed);

    let superposition_steps: Vec<usize> = result
        .iter()
        .filter(|(_, s)| s.rule.contains("superposition") || s.rule.contains("demodulation"))
        .map(|(&i, _)| i)
        .collect();

    assert!(
        !superposition_steps.is_empty(),
        "no superposition/demodulation steps remain after turnaround"
    );
}

#[test]
fn test_mixed_quantifiers_contrapositive() {
    // Simulate a small Vampire-like proof that triggers mixed quantifiers and contrapositive swap
    let proof_text = r#"
1. ! [X,Y] : f(X) = f(Y) [input]
2. ? [sK0] : f(a) != sK0 [negated conjecture 1]
3  ? [sK0] ! [Y] : f(Y) != sK0 [superposition 1,2]
4  ? [sK0] ! [Y] : f(Y) != sK0 [superposition 2,3]
5. $false  [superposition 3,4]
"#;

    let steps = parse_vampire_proof(proof_text);
    _debug_print_parsed_proof(&steps);
    let turned = turn_proof_around(&steps);
    println!("\n[TEST] Turned proof steps");
    for (idx, step) in &turned {
        println!("  {}: {}", idx, step.formula);
    }

    // Check that the contrapositive + Skolem-to-variable + quantifier flattening worked
    let step4_formula = &turned[&4].formula.to_string();
    println!(
        "\n[TEST] Step 4 formula after turnaround: {}",
        step4_formula
    );
    let step5_formula = &turned[&5].formula.to_string();
    println!(
        "\n[TEST] Step 5 formula after turnaround: {}",
        step5_formula
    );

    // Expectation:
    // - Forall over sK0 (converted to X0)
    // - Exists Y inside
    assert!(
        step4_formula.contains("! [X0] : (? [Y]"),
        "Step 4 should have mixed quantifiers ![X0] : ?[Y]"
    );
    assert!(
        step5_formula.contains("f(a) = X0") || step5_formula.contains("f(Y) != X0"),
        "Step 5 should have variable Y inside"
    );
}

#[test]
fn no_proof_turnaround() {
    let proof_text = r#"
% Running in auto input_syntax mode. Trying TPTP
% Refutation found. Thanks to Tanya!
% SZS status Theorem for Equation650_implies_Equation448
% SZS output start Proof for Equation650_implies_Equation448
2. ! [X0,X1,X2] : op(X0,op(X1,op(X2,op(X0,X2)))) = X0 [input]
3. ~! [X0,X1,X2] : op(X0,op(X1,op(X2,op(X0,X2)))) = X0 [negated conjecture 2]
30. ! [X0,X1,X2,X3] : op(X3,op(op(X1,op(op(X2,X1),X1)),X3)) = op(op(X3,op(op(X1,op(op(X2,X1),X1)),X3)),op(X0,op(op(X1,op(op(X2,X1),X1)),X0))) [input]
51. ! [X0,X1,X2] : op(X0,op(op(X1,X0),X0)) = op(op(X0,op(op(X1,X0),X0)),op(X2,op(op(X0,op(op(X1,X0),X0)),X2))) [input]
64. ! [X0,X1,X2] : op(X2,op(op(X0,op(op(X1,X0),X0)),X2)) = X2 [input]
71. ? [X0,X1,X2] : op(X0,op(X1,op(X2,op(X0,X2)))) != X0 [ennf transformation 3]
72. ? [X0,X1,X2] : op(X0,op(X1,op(X2,op(X0,X2)))) != X0 => sK0 != op(sK0,op(sK1,op(sK2,op(sK0,sK2)))) [choice axiom]
73. sK0 != op(sK0,op(sK1,op(sK2,op(sK0,sK2)))) [skolemisation 71,72]
75. sK0 != op(sK0,op(sK1,op(sK2,op(sK0,sK2)))) [cnf transformation 73]
102. op(X3,op(op(X1,op(op(X2,X1),X1)),X3)) = op(op(X3,op(op(X1,op(op(X2,X1),X1)),X3)),op(X0,op(op(X1,op(op(X2,X1),X1)),X0))) [cnf transformation 30]
123. op(X0,op(op(X1,X0),X0)) = op(op(X0,op(op(X1,X0),X0)),op(X2,op(op(X0,op(op(X1,X0),X0)),X2))) [cnf transformation 51]
136. op(X2,op(op(X0,op(op(X1,X0),X0)),X2)) = X2 [cnf transformation 64]
141. op(X0,op(op(X1,X0),X0)) = op(op(X0,op(op(X1,X0),X0)),X2) [backward demodulation 123,136]
143. op(X3,op(X0,op(op(X1,op(op(X2,X1),X1)),X0))) = X3 [backward demodulation 102,136]
144. op(X2,op(X0,op(op(X1,X0),X0))) = X2 [backward demodulation 136,141]
146. op(X3,op(X0,op(X1,op(op(X2,X1),X1)))) = X3 [forward demodulation 143,141]
147. op(X3,X0) = X3 [forward demodulation 146,144]
158. sK0 != op(sK0,sK1) [backward demodulation 75,147]
159. $false [subsumption resolution 158,147]
% SZS output end Proof for Equation650_implies_Equation448
% ------------------------------
% Version: Vampire 4.8 (commit )
% Termination reason: Refutation

% Memory used [KB]: 4989
% Time elapsed: 0.002 s
% ------------------------------
% ------------------------------
"#;

    let parsed = parse_vampire_proof(proof_text);
    let turned = turn_proof_around(&parsed);

    // Collect steps in index order
    let mut steps: Vec<(&usize, &SuperpositionStep)> = turned.iter().collect();
    steps.sort_by_key(|(i, _)| *i);

    // Get last two steps
    let (idx2, step2) = steps[steps.len() - 2];
    let (idx1, step1) = steps[steps.len() - 1];

    // Assertions on indices (optional but nice)
    assert_eq!(*idx2, 158);
    assert_eq!(*idx1, 159);

    // Assertions on formulas (exact)
    assert_eq!(
        step2.formula.to_string(),
        "! [X0,X1] : X0 = op(X0,X1)",
        "Unexpected second-to-last formula"
    );

    assert_eq!(
        step1.formula.to_string(),
        "! [X0,X1,X2] : X0 = op(X0,op(X1,op(X2,op(X0,X2))))",
        "Unexpected last formula"
    );
}

#[test]
fn proof_turnaround_dif() {
    let proof_text = r#"
% Running in auto input_syntax mode. Trying TPTP
% Refutation found. Thanks to Tanya!
% SZS status Theorem for Equation4417_implies_Equation4429
% SZS output start Proof for Equation4417_implies_Equation4429
1. ! [X0,X1,X2,X3] : op(X0,op(X0,X1)) = op(op(X2,X0),X2) [input]
2. ! [X0,X1,X2,X3] : op(X0,op(X0,X1)) = op(op(X2,X3),X2) [input]
3. ~! [X0,X1,X2,X3] : op(X0,op(X0,X1)) = op(op(X2,X3),X2) [negated conjecture 2]
4. ! [X0,X1,X2] : op(X0,op(X0,X1)) = op(op(X2,X0),X2) [rectify 1]
5. ? [X0,X1,X2,X3] : op(X0,op(X0,X1)) != op(op(X2,X3),X2) [ennf transformation 3]
6. ? [X0,X1,X2,X3] : op(X0,op(X0,X1)) != op(op(X2,X3),X2) => op(sK0,op(sK0,sK1)) != op(op(sK2,sK3),sK2) [choice axiom]
7. op(sK0,op(sK0,sK1)) != op(op(sK2,sK3),sK2) [skolemisation 5,6]
8. op(X0,op(X0,X1)) = op(op(X2,X0),X2) [cnf transformation 4]
9. op(sK0,op(sK0,sK1)) != op(op(sK2,sK3),sK2) [cnf transformation 7]
11. op(op(X7,op(X4,X5)),X7) = op(op(X4,X5),op(X5,op(X5,X6))) [superposition 8,8]
12. op(op(X2,X0),X2) = op(op(X3,X0),X3) [superposition 8,8]
15. op(X1,op(X1,X2)) = op(X1,op(X1,X3)) [superposition 8,8]
16. op(sK0,op(sK0,sK1)) != op(sK3,op(sK3,X0)) [superposition 9,8]
18. op(sK0,op(sK0,sK1)) != op(op(X1,sK3),X1) [superposition 16,8]
43. op(X8,op(X8,X11)) = op(X8,op(op(X10,X8),X10)) [superposition 15,8]
249. op(X17,op(X17,X19)) = op(op(X20,op(op(X17,op(X17,X18)),X17)),X20) [superposition 11,8]
273. op(sK0,op(sK0,sK1)) != op(op(X23,op(op(sK3,op(sK3,X22)),sK3)),X23) [superposition 18,11]
340. op(op(X60,op(X57,X58)),X60) = op(op(X57,op(op(X59,X57),X59)),X57) [superposition 12,43]
11843. op(sK0,op(sK0,sK1)) != op(op(X16,op(op(sK3,X15),X17)),X16) [superposition 273,340]
12695. op(sK0,op(sK0,sK1)) != op(op(X2,op(X2,X3)),X2) [superposition 11843,43]
14320. op(sK0,op(sK0,sK1)) != op(X48,op(X48,X50)) [superposition 12695,249]
15184. $false [equality resolution 14320]
% SZS output end Proof for Equation4417_implies_Equation4429
% ------------------------------
% Version: Vampire 4.8 (commit )
% Termination reason: Refutation

% Memory used [KB]: 29935
% Time elapsed: 0.301 s
% ------------------------------
% ------------------------------
"#;

    let steps_map = parse_vampire_proof(proof_text);
    _debug_print_parsed_proof(&steps_map);
    let final_proof = eq_proof_procedure(proof_text);
    println!("\n[TEST] Final proof");
    println!("{}", final_proof);
}
