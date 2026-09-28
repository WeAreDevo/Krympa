use regex::Regex;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt;

/// Term in equational logic
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    Var(String),
    Skolem(String),
    Fun(String, Vec<Term>),
}

/// AST for formulas with quantifiers
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Formula {
    Eq(Term, Term),
    Neq(Term, Term),
    Forall(Vec<String>, Box<Formula>),
    Exists(Vec<String>, Box<Formula>),
    Const(String), // $true or $false
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Formula::Eq(a, b) => {
                write!(f, "{} = {}", term_to_string(a), term_to_string(b))
            }
            Formula::Neq(a, b) => {
                write!(f, "{} != {}", term_to_string(a), term_to_string(b))
            }
            Formula::Forall(vars, inner_f) => {
                let inner = match **inner_f {
                    Formula::Forall(_, _) | Formula::Exists(_, _) => {
                        format!("({})", inner_f)
                    }
                    _ => inner_f.to_string(),
                };
                write!(f, "! [{}] : {}", vars.join(","), inner)
            }
            Formula::Exists(vars, inner_f) => {
                let inner = match **inner_f {
                    Formula::Forall(_, _) | Formula::Exists(_, _) => {
                        format!("({})", inner_f)
                    }
                    _ => inner_f.to_string(),
                };
                write!(f, "? [{}] : {}", vars.join(","), inner)
            }
            Formula::Const(c) => write!(f, "{}", c),
        }
    }
}

/// Pretty-print term
fn term_to_string(t: &Term) -> String {
    match t {
        Term::Var(s) => s.clone(),
        Term::Skolem(s) => s.clone(),
        Term::Fun(f, args) => {
            let inner: Vec<String> = args.iter().map(term_to_string).collect();
            format!("{}({})", f, inner.join(","))
        }
    }
}

/// Step in the proof
#[derive(Debug, Clone)]
pub struct SuperpositionStep {
    pub formula: Formula,
    pub deps: Vec<(usize, usize)>,
    pub is_negated_conjecture: bool,
    pub rule: String, // full rule name
}

/// Check if a rule is a real proof step
fn is_proof_step(rule: &str) -> bool {
    let core = rule
        .trim_start_matches("forward ")
        .trim_start_matches("backward ");
    core.starts_with("superposition")
        || core.starts_with("resolution")
        || core.starts_with("subsumption resolution")
        || core.starts_with("subsumption demodulation")
        || core.starts_with("factoring")
        || core.starts_with("equality factoring")
        || core.starts_with("equality resolution")
        || core.starts_with("inequality resolution")
        || core.starts_with("rewriting")
        || core.starts_with("demodulation")
        || core.starts_with("simplification")
        || core.starts_with("subsumption")
        || core.starts_with("distinctness")
        || core.starts_with("trivial inequality removal")
        || rule == "equality"
        || rule == "inequality"
}

/* ------------------ PARSING ------------------ */

/// Converts Vampire formula strings into Formula AST
/// Only handles equational logic with optional quantifiers
pub fn parse_formula(s: &str) -> Formula {
    let mut bound = BTreeSet::<String>::new();
    parse_formula_with_bound(s.trim(), &mut bound)
}

/// Parse formulas with possibly chained leading quantifiers.
/// Handles:
///   ! [X] : F
///   ? [X] : F
///   ? [X] ! [Y] : F   (colon after first binder is optional)
fn parse_formula_with_bound(s: &str, bound: &mut BTreeSet<String>) -> Formula {
    let s = s.trim();

    if s == "$false" || s == "$true" {
        return Formula::Const(s.to_string());
    }

    // quantifier head with OPTIONAL ":" so "? [sK0] ! [Y] : ..." parses.
    let qre = Regex::new(r"^([!?])\s*\[([^\]]*)\]\s*(?::\s*)?(.*)$").unwrap();
    if let Some(caps) = qre.captures(s) {
        let q = &caps[1];
        let vars: Vec<String> = caps[2]
            .split(',')
            .map(|v| v.trim().to_string())
            .filter(|v| !v.is_empty())
            .collect();
        let rest = caps[3].trim();

        // push scope
        for v in &vars {
            bound.insert(v.clone());
        }

        let inner = parse_formula_with_bound(rest, bound);

        // pop scope
        for v in &vars {
            bound.remove(v);
        }

        return if q == "!" {
            Formula::Forall(vars, Box::new(inner))
        } else {
            Formula::Exists(vars, Box::new(inner))
        };
    }

    // base Eq/Neq
    if let Some((lhs, rhs)) = s.split_once("!=") {
        Formula::Neq(parse_term(lhs, bound), parse_term(rhs, bound))
    } else if let Some((lhs, rhs)) = s.split_once('=') {
        Formula::Eq(parse_term(lhs, bound), parse_term(rhs, bound))
    } else {
        panic!("Cannot parse formula: {}", s);
    }
}

/// Parse term (simple)
fn parse_term(s: &str, bound: &BTreeSet<String>) -> Term {
    let s = s.trim();

    if let Some(caps) = Regex::new(r"^([a-zA-Z_][a-zA-Z0-9_]*)\((.*)\)$")
        .unwrap()
        .captures(s)
    {
        let f = caps[1].to_string();
        let args_str = &caps[2];
        let args: Vec<Term> = split_top_level(args_str, ',')
            .into_iter()
            .map(|t| parse_term(&t, bound))
            .collect();
        return Term::Fun(f, args);
    }

    // if the name is bound by a quantifier, it is a variable even if it starts with sK.
    if bound.contains(s) {
        return Term::Var(s.to_string());
    }

    if s.starts_with("sK") {
        Term::Skolem(s.to_string())
    } else {
        Term::Var(s.to_string())
    }
}

/// Split top-level comma-separated terms
fn split_top_level(s: &str, sep: char) -> Vec<String> {
    let mut res = Vec::new();
    let mut depth = 0;
    let mut buf = String::new();
    for c in s.chars() {
        match c {
            '(' => {
                depth += 1;
                buf.push(c);
            }
            ')' => {
                depth -= 1;
                buf.push(c);
            }
            c if c == sep && depth == 0 => {
                res.push(buf.trim().to_string());
                buf.clear();
            }
            _ => buf.push(c),
        }
    }
    if !buf.trim().is_empty() {
        res.push(buf.trim().to_string());
    }
    res
}

/// Don't strip quantifier colons. Only strip genuine "label: formula" prefixes.
fn strip_optional_label(s: &str) -> &str {
    let s = s.trim();

    if s.starts_with('!') || s.starts_with('?') {
        return s;
    }

    if let Some((lhs, rhs)) = s.split_once(':') {
        let lhs = lhs.trim();
        let looks_like_label = !lhs.is_empty()
            && !lhs.contains(' ')
            && !lhs.contains('=')
            && !lhs.contains('!')
            && !lhs.contains('?')
            && !lhs.contains('(');

        if looks_like_label {
            return rhs.trim();
        }
    }

    s
}

/// Parse the bracket part, e.g.
///   "backward demodulation 8,13"
///   "subsumption resolution 30,21"
///   "negated conjecture 2"
/// Returns: (rule_full, deps, is_negated_conjecture)
fn parse_inf_bracket(inf: &str) -> (String, Vec<usize>, bool) {
    let inf = inf.trim().trim_end_matches(']').trim();

    let is_neg = inf.contains("negated conjecture");

    // deps: collect all integers anywhere
    let deps: Vec<usize> = inf
        .split(|c: char| c == ',' || c.is_whitespace())
        .filter_map(|tok| tok.parse::<usize>().ok())
        .collect();

    // rule_full: take all non-numeric words, excluding "negated conjecture"
    let mut words: Vec<String> = Vec::new();
    let toks: Vec<&str> = inf.split_whitespace().collect();

    let mut i = 0;
    while i < toks.len() {
        let tok = toks[i].trim_end_matches(',');

        // skip numeric tokens
        if tok.chars().all(|c| c.is_ascii_digit()) {
            i += 1;
            continue;
        }

        // skip "negated conjecture" tokens, but remember they were there
        if tok == "negated" && i + 1 < toks.len() && toks[i + 1] == "conjecture" {
            i += 2;
            continue;
        }

        // keep other words
        if tok.chars().any(|c| c.is_alphabetic()) {
            words.push(tok.to_string());
        }
        i += 1;
    }

    let rule_full = if !words.is_empty() {
        words.join(" ")
    } else if is_neg {
        "negated conjecture".to_string()
    } else {
        "unknown".to_string()
    };

    (rule_full, deps, is_neg)
}

/// Parse Vampire proof into steps (robust-ish)
pub fn parse_vampire_proof(proof_text: &str) -> BTreeMap<usize, SuperpositionStep> {
    let mut steps_map = BTreeMap::new();
    let line_re = Regex::new(r"^\s*(\d+)\s*[.]?\s*(.*)$").unwrap();

    for line in proof_text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('%') {
            continue;
        }

        let caps = match line_re.captures(line) {
            Some(c) => c,
            None => continue,
        };

        let idx: usize = caps[1].parse().unwrap();
        let rest = caps[2].trim();

        // split off optional inference/dependency part in brackets
        let (before_inf, inf_part) = match rest.rsplit_once('[') {
            Some((b, i)) => (b.trim(), Some(i)),
            None => (rest.trim(), None),
        };

        let formula_str = strip_optional_label(before_inf);
        let formula = parse_formula(formula_str);

        let mut is_negated_conjecture = false;
        let mut rule = "unknown".to_string();
        let mut deps = Vec::new();

        if let Some(inf) = inf_part {
            let inf = inf.trim_end_matches(']').trim();

            let (rule_full, deps_nums, is_neg) = parse_inf_bracket(inf);

            is_negated_conjecture = is_neg;
            rule = rule_full;

            deps = deps_nums.into_iter().map(|d| (0, d)).collect();
        }

        steps_map.insert(
            idx,
            SuperpositionStep {
                formula,
                deps,
                is_negated_conjecture,
                rule,
            },
        );
    }

    steps_map
}

/* ------------------ DEPENDENCIES ------------------ */

fn build_forward_deps(steps: &BTreeMap<usize, SuperpositionStep>) -> BTreeMap<usize, Vec<usize>> {
    let mut forward: BTreeMap<usize, Vec<usize>> = BTreeMap::new();

    for (&idx, step) in steps {
        for &(_, dep) in &step.deps {
            forward.entry(dep).or_default().push(idx);
        }
    }

    forward
}

fn gather_forward_chain(
    start: usize,
    forward: &BTreeMap<usize, Vec<usize>>,
    visited: &mut BTreeSet<usize>,
) {
    if !visited.insert(start) {
        return;
    }
    if let Some(nexts) = forward.get(&start) {
        for &n in nexts {
            gather_forward_chain(n, forward, visited);
        }
    }
}

/* ------------------ NEGATED CHAIN ------------------ */

struct NegChain {
    start: Option<usize>,
    chain_set: BTreeSet<usize>,
    forward: BTreeMap<usize, Vec<usize>>,
}

fn compute_neg_chain(steps: &BTreeMap<usize, SuperpositionStep>) -> Option<NegChain> {
    let forward = build_forward_deps(steps);

    let neg_roots: Vec<usize> = steps
        .iter()
        .filter(|(_, s)| s.is_negated_conjecture)
        .map(|(&i, _)| i)
        .collect();

    if neg_roots.is_empty() {
        return None;
    }

    let mut chain = BTreeSet::new();
    for &r in &neg_roots {
        gather_forward_chain(r, &forward, &mut chain);
    }

    let chain_vec: Vec<usize> = chain.iter().cloned().collect();

    let mut start = None;
    for (pos, &i) in chain_vec.iter().enumerate() {
        if is_proof_step(&steps[&i].rule) {
            start = pos.checked_sub(1).map(|p| chain_vec[p]);
            break;
        }
    }

    Some(NegChain {
        start,
        chain_set: chain,
        forward,
    })
}
/* ------------------ Trivial EQUALITY ELIMINATION ------------------ */

fn is_reflexive_eq(f: &Formula) -> bool {
    match f {
        Formula::Eq(a, b) => a == b,
        Formula::Forall(_, sub) | Formula::Exists(_, sub) => is_reflexive_eq(sub),
        _ => false,
    }
}

fn is_reflexive_neq(f: &Formula) -> bool {
    match f {
        Formula::Neq(a, b) => a == b,
        Formula::Forall(_, sub) | Formula::Exists(_, sub) => is_reflexive_neq(sub),
        _ => false,
    }
}

/// “Trivial” steps we don't want to count/print/use as explicit premises:
/// - reflexive equality: t = t  (possibly under quantifiers)
/// - (optionally) reflexive disequality: t != t  (usually only appears briefly)
/// - the turned-around equality-resolution node: $true [equality ...]
fn is_trivial_step(step: &SuperpositionStep) -> bool {
    if is_reflexive_eq(&step.formula) || is_reflexive_neq(&step.formula) {
        return true;
    }

    // turned equality-resolution node becomes $true and should be eliminated
    if step.rule == "equality" {
        if let Formula::Const(c) = &step.formula {
            if c == "$true" {
                return true;
            }
        }
    }

    false
}

/// Remove dependencies that point to trivial steps, propagating their deps upward.
/// If step A depends on trivial step T which depends on [B, C], A inherits [B, C].
fn drop_trivial_deps(steps: &mut BTreeMap<usize, SuperpositionStep>) {
    let trivial: BTreeSet<usize> = steps
        .iter()
        .filter_map(|(&i, s)| if is_trivial_step(s) { Some(i) } else { None })
        .collect();

    // collect trivial step deps once
    let trivial_deps: HashMap<usize, Vec<(usize, usize)>> = trivial
        .iter()
        .filter_map(|&t| steps.get(&t).map(|s| (t, s.deps.clone())))
        .collect();

    for (_, step) in steps.iter_mut() {
        let mut new_deps: Vec<(usize, usize)> = Vec::new();
        for &(lvl, d) in &step.deps {
            if trivial.contains(&d) {
                // substitute: inherit the trivial step's own deps
                if let Some(inherited) = trivial_deps.get(&d) {
                    new_deps.extend(inherited.iter().copied());
                }
                // if the trivial step has no deps, it is dropped silently
            } else {
                new_deps.push((lvl, d));
            }
        }
        // deduplicate while preserving order
        let mut seen = BTreeSet::new();
        step.deps = new_deps
            .into_iter()
            .filter(|&(_, d)| seen.insert(d))
            .collect();
    }
}

/// remove trivial steps from the map
/// IMPORTANT: indices become “gappy” (fine) unless we renumber (TODO)
fn remove_trivial_steps(steps: &mut BTreeMap<usize, SuperpositionStep>) {
    let trivial_ids: Vec<usize> = steps
        .iter()
        .filter_map(|(&i, s)| if is_trivial_step(s) { Some(i) } else { None })
        .collect();

    for i in trivial_ids {
        steps.remove(&i);
    }
}

/// A true step count
pub fn _count_nontrivial_steps(steps: &BTreeMap<usize, SuperpositionStep>) -> usize {
    steps.values().filter(|s| !is_trivial_step(s)).count()
}

/* ------------------ CORE LOGIC: CONTRAPOSITIVE (EQUATIONAL) ------------------ */

fn core_is_diseq(f: &Formula) -> bool {
    match f {
        Formula::Neq(_, _) => true,
        Formula::Eq(_, _) | Formula::Const(_) => false,
        Formula::Forall(_, sub) | Formula::Exists(_, sub) => core_is_diseq(sub),
    }
}

/// Negate in an equational setting:
/// - Eq <-> Neq under polarity
/// - ∀ <-> ∃ under polarity
/// - Constants unchanged (we handle $false -> $true separately for proof-turning)
fn contrapose_formula(f: &Formula, polarity: bool) -> Formula {
    match f {
        Formula::Eq(a, b) => {
            if polarity {
                Formula::Neq(a.clone(), b.clone())
            } else {
                Formula::Eq(a.clone(), b.clone())
            }
        }
        Formula::Neq(a, b) => {
            if polarity {
                Formula::Eq(a.clone(), b.clone())
            } else {
                Formula::Neq(a.clone(), b.clone())
            }
        }
        Formula::Forall(vars, sub) => {
            if polarity {
                Formula::Exists(vars.clone(), Box::new(contrapose_formula(sub, polarity)))
            } else {
                Formula::Forall(vars.clone(), Box::new(contrapose_formula(sub, polarity)))
            }
        }
        Formula::Exists(vars, sub) => {
            if polarity {
                Formula::Forall(vars.clone(), Box::new(contrapose_formula(sub, polarity)))
            } else {
                Formula::Exists(vars.clone(), Box::new(contrapose_formula(sub, polarity)))
            }
        }
        Formula::Const(c) => Formula::Const(c.clone()),
    }
}

/// Replace Skolem constants (Term::Skolem) with fresh variables (X0, X1, ...).
/// This is ONLY for actual Term::Skolem occurrences (not bound vars).
fn skolem_to_variable(f: &Formula) -> Formula {
    let mut map: HashMap<String, String> = HashMap::new();
    let mut counter: usize = 0;

    fn walk_term(t: &Term, map: &mut HashMap<String, String>, counter: &mut usize) -> Term {
        match t {
            Term::Skolem(s) => {
                let v = map.entry(s.clone()).or_insert_with(|| {
                    let name = format!("X{}", *counter);
                    *counter += 1;
                    name
                });
                Term::Var(v.clone())
            }
            Term::Var(v) => Term::Var(v.clone()),
            Term::Fun(f, args) => Term::Fun(
                f.clone(),
                args.iter().map(|a| walk_term(a, map, counter)).collect(),
            ),
        }
    }

    fn walk(f: &Formula, map: &mut HashMap<String, String>, counter: &mut usize) -> Formula {
        match f {
            Formula::Eq(a, b) => {
                Formula::Eq(walk_term(a, map, counter), walk_term(b, map, counter))
            }
            Formula::Neq(a, b) => {
                Formula::Neq(walk_term(a, map, counter), walk_term(b, map, counter))
            }
            Formula::Forall(vars, sub) => {
                Formula::Forall(vars.clone(), Box::new(walk(sub, map, counter)))
            }
            Formula::Exists(vars, sub) => {
                Formula::Exists(vars.clone(), Box::new(walk(sub, map, counter)))
            }
            Formula::Const(c) => Formula::Const(c.clone()),
        }
    }

    walk(f, &mut map, &mut counter)
}

/// Flatten consecutive same-kind quantifiers (∀∀..., ∃∃...).
fn flatten_quantifiers(f: Formula) -> Formula {
    match f {
        Formula::Forall(mut vars, sub) => {
            let inner = flatten_quantifiers(*sub);
            match inner {
                Formula::Forall(mut inner_vars, inner_sub) => {
                    vars.append(&mut inner_vars);
                    Formula::Forall(vars, inner_sub)
                }
                other => Formula::Forall(vars, Box::new(other)),
            }
        }
        Formula::Exists(mut vars, sub) => {
            let inner = flatten_quantifiers(*sub);
            match inner {
                Formula::Exists(mut inner_vars, inner_sub) => {
                    vars.append(&mut inner_vars);
                    Formula::Exists(vars, inner_sub)
                }
                other => Formula::Exists(vars, Box::new(other)),
            }
        }
        other => other,
    }
}

/// Cosmetic but requested: rename bound variables that look like sK\d+ to X0,X1,...
/// This is scope-safe (handles shadowing).
fn rename_skolem_like_bound_vars(f: &Formula) -> Formula {
    let sk_like = Regex::new(r"^sK\d+$").unwrap();
    let mut counter: usize = 0;

    fn rename_term(t: &Term, env: &Vec<HashMap<String, String>>) -> Term {
        match t {
            Term::Var(v) => {
                for scope in env.iter().rev() {
                    if let Some(nv) = scope.get(v) {
                        return Term::Var(nv.clone());
                    }
                }
                Term::Var(v.clone())
            }
            Term::Skolem(s) => Term::Skolem(s.clone()),
            Term::Fun(f, args) => Term::Fun(
                f.clone(),
                args.iter().map(|a| rename_term(a, env)).collect(),
            ),
        }
    }

    fn walk(
        f: &Formula,
        sk_like: &Regex,
        counter: &mut usize,
        env: &mut Vec<HashMap<String, String>>,
    ) -> Formula {
        match f {
            Formula::Forall(vars, sub) => {
                let mut scope: HashMap<String, String> = HashMap::new();
                let mut new_vars: Vec<String> = Vec::with_capacity(vars.len());
                for v in vars {
                    if sk_like.is_match(v) {
                        let nv = format!("X{}", *counter);
                        *counter += 1;
                        scope.insert(v.clone(), nv.clone());
                        new_vars.push(nv);
                    } else {
                        new_vars.push(v.clone());
                    }
                }
                env.push(scope);
                let new_sub = walk(sub, sk_like, counter, env);
                env.pop();
                Formula::Forall(new_vars, Box::new(new_sub))
            }
            Formula::Exists(vars, sub) => {
                let mut scope: HashMap<String, String> = HashMap::new();
                let mut new_vars: Vec<String> = Vec::with_capacity(vars.len());
                for v in vars {
                    if sk_like.is_match(v) {
                        let nv = format!("X{}", *counter);
                        *counter += 1;
                        scope.insert(v.clone(), nv.clone());
                        new_vars.push(nv);
                    } else {
                        new_vars.push(v.clone());
                    }
                }
                env.push(scope);
                let new_sub = walk(sub, sk_like, counter, env);
                env.pop();
                Formula::Exists(new_vars, Box::new(new_sub))
            }
            Formula::Eq(a, b) => Formula::Eq(rename_term(a, env), rename_term(b, env)),
            Formula::Neq(a, b) => Formula::Neq(rename_term(a, env), rename_term(b, env)),
            Formula::Const(c) => Formula::Const(c.clone()),
        }
    }

    let mut env: Vec<HashMap<String, String>> = Vec::new();
    walk(f, &sk_like, &mut counter, &mut env)
}

/* ------------------ CONTRAPOSITIVE SWAP ------------------ */

/// Collect all variables (Var + Skolem) in a term
fn collect_vars(t: &Term, vars: &mut BTreeSet<String>) {
    match t {
        Term::Var(v) => {
            vars.insert(v.clone());
        }
        Term::Skolem(s) => {
            vars.insert(s.clone());
        }
        Term::Fun(_, args) => {
            for a in args {
                collect_vars(a, vars);
            }
        }
    }
}

/// Collect all variables in a formula recursively
fn formula_vars(f: &Formula) -> BTreeSet<String> {
    let mut vars = BTreeSet::new();
    match f {
        Formula::Eq(a, b) | Formula::Neq(a, b) => {
            collect_vars(a, &mut vars);
            collect_vars(b, &mut vars);
        }
        Formula::Forall(vs, sub) | Formula::Exists(vs, sub) => {
            for v in vs {
                vars.insert(v.clone());
            }
            vars.extend(formula_vars(sub));
        }
        Formula::Const(_) => {}
    }
    vars
}

/// Contrapositive swap:
/// - recurse along forward edges inside `chain`
/// - if the step is (core) disequality: negate it to equality, replace Skolems with fresh Xk vars
/// - universally quantify those newly introduced Xk vars
/// - keep a stable traversal order in `order`
fn contrapositive_swap(
    idx: usize,
    steps: &mut BTreeMap<usize, SuperpositionStep>,
    forward: &BTreeMap<usize, Vec<usize>>,
    visited: &mut BTreeSet<usize>,
    order: &mut Vec<usize>,
    chain: &BTreeSet<usize>,
) {
    if !chain.contains(&idx) || !visited.insert(idx) {
        return;
    }

    // Recurse first so `order` becomes a post-order (useful for later re-threading).
    if let Some(nexts) = forward.get(&idx) {
        for &n in nexts.iter().filter(|n| chain.contains(n)) {
            contrapositive_swap(n, steps, forward, visited, order, chain);
        }
    }

    if let Some(step) = steps.get_mut(&idx) {
        // 0) Special case: refutation node
        if let Formula::Const(c) = &step.formula {
            if c == "$false" {
                step.formula = Formula::Const("$true".to_string());
                order.push(idx);
                return;
            }
        }

        if core_is_diseq(&step.formula) {
            // 1) Save vars before (we only care about existing Xk vars to detect fresh ones later).
            let before = formula_vars(&step.formula);
            let before_x: BTreeSet<String> = before
                .into_iter()
                .filter(|v| v.starts_with('X')) // only track the "fresh" namespace
                .collect();

            // 2) Flip polarity: Neq -> Eq (and handles quantifiers if present)
            let mut f = contrapose_formula(&step.formula, true);

            // 3) Replace Skolem constants with fresh Xk variables
            f = skolem_to_variable(&f);

            // 4) Flatten quantifiers (purely structural/cosmetic)
            f = flatten_quantifiers(f);

            // 5) Cosmetic rename of bound vars that look like sK\d+
            f = rename_skolem_like_bound_vars(&f);

            // 6) Compute *new* X vars introduced by skolem_to_variable
            let after = formula_vars(&f);
            let after_x: BTreeSet<String> =
                after.into_iter().filter(|v| v.starts_with('X')).collect();

            let mut new_xs: Vec<String> = after_x.difference(&before_x).cloned().collect();
            new_xs.sort(); // deterministic printing and quantifier order

            // 7) Bind them universally (Skolems -> universally quantified vars)
            if !new_xs.is_empty() {
                f = Formula::Forall(new_xs.clone(), Box::new(f));
            }

            step.formula = f;
        }
    }

    order.push(idx);
}

/* ------------------ TURN PROOF AROUND ------------------ */

pub fn turn_proof_around(
    steps: &BTreeMap<usize, SuperpositionStep>,
) -> BTreeMap<usize, SuperpositionStep> {
    let Some(chain) = compute_neg_chain(steps) else {
        crate::klog_debug!(
            "[DEBUG] turn_proof_around: no negated conjecture chain found — skipping turnaround"
        );
        return steps.clone();
    };

    let Some(start) = chain.start else {
        crate::klog_debug!("[DEBUG] turn_proof_around: negated chain found but no proof-step start — skipping turnaround");
        return steps.clone();
    };

    let mut new_steps = steps.clone();
    let mut visited = BTreeSet::new();
    let mut order = Vec::new();

    contrapositive_swap(
        start,
        &mut new_steps,
        &chain.forward,
        &mut visited,
        &mut order,
        &chain.chain_set,
    );

    //println!("\n[DEBUG] Turn order {:?}", order);

    let mut result = steps.clone();
    for (old, new) in order.iter().zip(order.iter().rev()) {
        let mut step = new_steps[old].clone();
        step.rule = steps[new].rule.clone();
        step.deps = steps[new].deps.clone();
        result.insert(*new, step);
    }

    // treat t=t and turned equality-resolution as trivial
    drop_trivial_deps(&mut result);

    // actually remove them from the proof object
    remove_trivial_steps(&mut result);

    result
}

/* ------------------ TOP-LEVEL PROCEDURE ------------------ */

pub fn eq_proof_procedure(proof_text: &str) -> String {
    let parsed = parse_vampire_proof(proof_text);

    // always turn the proof
    let final_steps = turn_proof_around(&parsed);

    // _debug_print_parsed_proof(&parsed);
    // println!("\n[DEBUG] Contrapositive Vampire proof");
    // println!("{}", formatted);
    // println!("-------------------------------");

    format_proof(&final_steps)
}

/* ------------------ DEBUG ------------------ */

pub fn _debug_print_parsed_proof(steps: &BTreeMap<usize, SuperpositionStep>) {
    crate::klog_debug!("[DEBUG] Parsed Vampire proof");
    for (idx, step) in steps {
        crate::klog_debug!(
            "{:>4}. formula = {:?}, deps = {:?}, is_neg = {:?}, rule = {:?}",
            idx,
            step.formula.to_string(),
            step.deps,
            step.is_negated_conjecture,
            step.rule
        );
    }
    crate::klog_debug!("-------------------------------");
}

/// Format a proof (BTreeMap<usize, SuperpositionStep>) as Vampire-style text
/// Format a proof (BTreeMap<usize, SuperpositionStep>) as Vampire-style text
/// Desired bracket style: [rule dep1,dep2] (Vampire-ish)
pub fn format_proof(steps: &BTreeMap<usize, SuperpositionStep>) -> String {
    let mut lines = Vec::new();

    for (&idx, step) in steps {
        let formula_str = step.formula.to_string();

        // deps like "1,2" (no spaces)
        let deps_str = step
            .deps
            .iter()
            .map(|(_, d)| d.to_string())
            .collect::<Vec<_>>()
            .join(",");

        // Decide what goes in [...]
        let mut parts: Vec<String> = Vec::new();

        // Put rule first (if known), then deps
        let rule = step.rule.trim();
        if !rule.is_empty() && rule != "unknown" {
            if deps_str.is_empty() {
                parts.push(rule.to_string());
            } else {
                parts.push(format!("{} {}", rule, deps_str));
            }
        } else if !deps_str.is_empty() {
            // no rule, but deps exist
            parts.push(deps_str.clone());
        }

        let mut line = format!("{}. {}", idx, formula_str);

        if !parts.is_empty() {
            line.push_str(" [");
            line.push_str(&parts.join(", "));
            line.push(']');
        }

        lines.push(line);
    }

    lines.join("\n")
}
