use krympa::alpha_match::formulas_match;
use krympa::alpha_match::formulas_match_with_permutations;
use krympa::alpha_match::normalize_formula_alpha;

#[test]
fn test_match() {
    let twee = "(op(V0,op(op(V1,V0),V2))=V3)";
    let vamp = "(op(X5,op(op(X6,X5),X7))=X8)";
    assert!(formulas_match(twee, vamp));
}

#[test]
fn test_non_match() {
    let twee = "(op(V0,V1)=V2)";
    let vamp = "(op(X0,op(X1,X0))=X1)";
    assert!(!formulas_match(twee, vamp));
}

#[test]
fn test_match_same() {
    let twee = "(op(X0,X1)=X2)";
    let vamp = "(op(X8,X3)=X4)";
    assert!(formulas_match(twee, vamp));
}

#[test]
fn test_non_match_same() {
    let twee = "(op(X0,op(X1,X0))=X1)";
    let vamp = "(op(X0,X0)=X1)";
    assert!(!formulas_match(twee, vamp));
}

#[test]
fn test_non_match_same_args() {
    let twee = "(op(X0,X1)=X1)";
    let vamp = "(op(X0,X0)=X1)";
    assert!(!formulas_match(twee, vamp));
}

#[test]
fn test_var() {
    let twee = "(op(X0,X1)=X1)";
    let vamp = "(op(X0,X1)=op(X0,X1))";
    assert!(!formulas_match(twee, vamp));
}

#[test]
fn test_non_match_twee_vamp() {
    let twee = "(op(V3,op(op(V1,op(op(V2,V1),V1)),V3))=op(op(V3,op(op(V1,op(op(V2,V1),V1)),V3)),op(V0,op(op(V1,op(op(V2,V1),V1)),V0))))";
    let vamp = "(op(V0,op(op(V1,op(op(V2,V3),V1)),V0))=op(op(V0,op(op(V1,op(op(V2,V3),V1)),V0)),op(V4,op(op(V5,op(V3,V5)),V4))))";
    assert!(!formulas_match(twee, vamp));
}

#[test]
fn test_match_orig() {
    let twee = "! [X, Y] : (op(Y, X) = Y)";
    let vamp = "! [X0, X1] :
        (op(X1,X0) = X1)";
    assert!(formulas_match(twee, vamp));
}

#[test]
fn test_match_orig_rev() {
    let twee = "! [X, Y] : (op(X, Y) = X)";
    let vamp = "! [X0, X1] :
        (op(X1,X0) = X1)";
    assert!(formulas_match(twee, vamp));
}

#[test]
fn test_match_from_example1() {
    let f1 = "! [X0,X1,X2,X3] : op(X0,X3) = op(op(X3,op(op(op(X0,X2),X1),X0)),X0)";
    let f2 = "op(X4,X8) = op(op(X8,op(op(op(X4,X6),X5),X4)),X4)";
    assert!(formulas_match(f1, f2));
}

#[test]
fn test_match_from_example2() {
    let f1 = "! [X0,X1,X2,X3] : op(X1,op(X0,op(op(X1,X2),X3))) = op(op(op(X1,X2),X0),X1)";
    let f2 = "op(X1,op(X0,op(op(X1,X2),X3))) = op(op(op(X1,X2),X0),X1)";
    assert!(formulas_match(f1, f2));
}

#[test]
fn test_match_from_example3() {
    let f1 = "! [X0, X1, X2] : (op(X1,X2) = op(op(X0,X1),X2))";
    let f2 = "op(x1, x2) = op(op(x0, x1), x2)";
    assert!(formulas_match(f1, f2));
}

#[test]
fn test_no_match_from_example4() {
    let f1 = "! [X0,X1,X2] : op(X0,X1) = op(op(X1,op(X2,X0)),X0)";
    let f2 = "op(X0,X3) = op(op(X3,op(X1,X0)),X0)";
    assert!(formulas_match(f1, f2));
}

#[test]
fn test_no_match_from_example() {
    let f1 = "! [X0, X1, X2] :
    (op(X0,X1) = op(op(X1,op(X0,X2)),X0))";
    let f2 = "! [X0, X1, X2] :
    (op(X0,X1) = op(op(X1,op(X2,X0)),X0))";
    assert!(!formulas_match(f1, f2));
}

#[test]
fn test_norm1() {
    let form = "! [X, Y] : (op(X, Y) = X)";
    let norm_form = "(op(V0,V1)=V0)";
    assert!(normalize_formula_alpha(form) == norm_form);
}

#[test]
fn test_norm2() {
    let form = "(op(X1,X0) = X1)";
    let norm_form = "(op(V0,V1)=V0)";
    assert!(normalize_formula_alpha(form) == norm_form);
}

#[test]
fn test_norm3() {
    let form = "! [X0, X1] :
        (op(X1,X0) = X1)";
    let norm_form = "(op(V1,V0)=V1)";
    assert!(normalize_formula_alpha(form) == norm_form);
}

#[test]
fn test_twee_formulas() {
    let twee1 = "! [X, Y, Z] : (op(X, op(op(Y, op(op(Z, Y), Y)), X)) = X)";
    let twee2 = "! [X, Y] : (op(X, Y) = X)";
    assert!(!formulas_match(twee1, twee2));
}

#[test]
fn test_vampire_formulas() {
    let formula1 = "! [X0, X1, X2, X3] : (op(X3,op(op(X1,op(op(X2,X1),X1)),X3)) = op(op(X3,op(op(X1,op(op(X2,X1),X1)),X3)),op(X0,op(op(X1,op(op(X2,X1),X1)),X0))))";
    let formula2 = "(op(X48,op(op(X45,op(op(X46,X45),X45)),X48)) = op(op(X48,op(op(X45,op(op(X46,X45),X45)),X48)),op(X44,op(op(X45,op(op(X46,X45),X45)),X44))))";
    assert!(formulas_match(formula1, formula2));
}

// ── formulas_match_with_permutations: reversed equality direction ─────────────

#[test]
fn test_permutations_reversed_equality_matches() {
    let formula = "! [X, Y] : (op(X,Y) = op(Y,X))";
    let target = "(op(V1,V0) = op(V0,V1))"; // sides swapped
    assert!(formulas_match_with_permutations(formula, target));
}

#[test]
fn test_permutations_reversed_equality_no_false_positive() {
    let formula = "! [X, Y] : (op(X,Y) = X)";
    let target = "(op(X0,X1) = op(X1,X0))";
    assert!(!formulas_match_with_permutations(formula, target));
}

#[test]
fn test_permutations_no_quant_reversed() {
    // No quantifier → large-formula branch; reversed sides should still match.
    let formula = "(op(X0,X1) = op(X1,X0))";
    let target = "(op(V1,V0) = op(V0,V1))";
    assert!(formulas_match_with_permutations(formula, target));
}

#[test]
fn test_permutations_small_vars_reversed() {
    let formula = "! [X, Y, Z] : (op(X,op(Y,Z)) = op(op(X,Y),Z))";
    let target = "(op(op(V0,V1),V2) = op(V0,op(V1,V2)))"; // sides swapped
    assert!(formulas_match_with_permutations(formula, target));
}
