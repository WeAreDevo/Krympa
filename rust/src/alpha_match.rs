use itertools::Itertools;
use regex::Regex;
use std::collections::{BTreeMap, HashMap};

#[derive(Debug, Clone, PartialEq, Eq)]
enum Term {
    Var(String),
    Fun(String, Vec<Term>),
}

/// Treat these as variables:
///   - V0, V1, ...
///   - X0, X1, ...
///   - x0, x1, ...
fn is_var_atom(s: &str) -> bool {
    let b = s.as_bytes();
    if b.is_empty() {
        return false;
    }
    let first = b[0];
    (first == b'V' || first == b'X' || first == b'x')
        && b.len() > 1
        && s[1..].bytes().all(|c| (c as char).is_ascii_digit())
}

/// Normalize formula with alpha-renaming of quantified variables
/// Quantified variables are renamed in order: V0, V1, ...
/// Unquantified X-style variables are normalized separately.
/// Output has all whitespace removed.
pub fn normalize_formula_alpha(formula: &str) -> String {
    // regex to extract leading quantifier: ! [X,Y,...] : body
    let quant_re = Regex::new(r"!\s*\[([^\]]*)\]\s*:\s*(.*)").unwrap();

    let mut normalized_body = if let Some(cap) = quant_re.captures(formula) {
        // extract quantified variables
        let vars: Vec<&str> = cap[1].split(',').map(|v| v.trim()).collect();
        let mut body = cap[2].trim().to_string();

        // replace each quantified variable consistently
        for (i, var) in vars.iter().enumerate() {
            let canon_var = format!("V{}", i);
            let var_re = Regex::new(&format!(r"\b{}\b", regex::escape(var))).unwrap();
            body = var_re.replace_all(&body, canon_var.as_str()).to_string();
        }

        body
    } else {
        formula.to_string()
    };

    // normalize any remaining X-style variables (unquantified)
    let var_re = Regex::new(r"\bX\d+\b").unwrap();
    let mut var_map: BTreeMap<String, String> = BTreeMap::new();
    let mut counter = 0usize;

    normalized_body = var_re
        .replace_all(&normalized_body, |caps: &regex::Captures| {
            let v = &caps[0];
            if !var_map.contains_key(v) {
                var_map.insert(v.to_string(), format!("V{}", counter));
                counter += 1;
            }
            var_map[v].clone()
        })
        .to_string();

    // remove all whitespace for canonical comparison
    normalized_body
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect()
}

/// Split a string at top-level occurrences of a delimiter (not inside parentheses).
fn split_top_level_by_char(s: &str, delim: char) -> Option<(String, String)> {
    let mut depth = 0i32;
    for (i, c) in s.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => depth -= 1,
            _ => {}
        }
        if depth == 0 && c == delim {
            let left = s[..i].to_string();
            let right = s[i + c.len_utf8()..].to_string();
            return Some((left, right));
        }
    }
    None
}

/// Parse an equation like:
///   "(op(V0,op(V1,V0))=V3)"
///   "op(V0,V1)=V0"
fn parse_equation(s: &str) -> Option<(Term, Term)> {
    let mut t = s.trim().to_string();

    // strip one layer of outer parentheses if present
    if t.starts_with('(') && t.ends_with(')') && t.len() >= 2 {
        t = t[1..t.len() - 1].to_string();
    }

    let (lhs_s, rhs_s) = split_top_level_by_char(&t, '=')?;
    let lhs = parse_term_std(&lhs_s)?;
    let rhs = parse_term_std(&rhs_s)?;
    Some((lhs, rhs))
}

/// Parse a term in standard syntax:
///   - variables: V0, X12, x3
///   - constants: a1, c0, foo
///   - functions: op(t1,t2,...) or f()
fn parse_term_std(s: &str) -> Option<Term> {
    let s = s.trim();
    if s.is_empty() {
        return None;
    }

    // If it contains no '(' at all, it's an atom
    if !s.contains('(') {
        if is_var_atom(s) {
            return Some(Term::Var(s.to_string()));
        } else {
            return Some(Term::Fun(s.to_string(), vec![]));
        }
    }

    // Parse function name up to first '('
    let open = s.find('(')?;
    let name = &s[..open];
    let mut rest = &s[open + 1..];
    if !rest.ends_with(')') {
        return None;
    }
    rest = &rest[..rest.len() - 1]; // inside (...)

    let args = split_args_top_level(rest)
        .into_iter()
        .map(|a| parse_term_std(&a))
        .collect::<Option<Vec<_>>>()?;

    Some(Term::Fun(name.to_string(), args))
}

/// Split function arguments at top-level commas.
fn split_args_top_level(s: &str) -> Vec<String> {
    let mut result = Vec::new();
    let mut depth = 0i32;
    let mut start = 0usize;

    for (i, c) in s.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => depth -= 1,
            ',' if depth == 0 => {
                result.push(s[start..i].to_string());
                start = i + 1;
            }
            _ => {}
        }
    }
    if start <= s.len() {
        result.push(s[start..].to_string());
    }
    result
        .into_iter()
        .map(|x| x.trim().to_string())
        .filter(|x| !x.is_empty())
        .collect()
}

pub fn formulas_match(formula: &str, other_formula: &str) -> bool {
    formulas_match_with_permutations(formula, other_formula)
}

/// Pattern match formula onto other_formula with variable map
/// Alpha-match terms with a variable->variable bijection.
/// - Variables can only match variables (not arbitrary subterms).
/// - Mapping is injective (no two vars map to the same target var).
fn match_terms_alpha(
    formula: &Term,
    other: &Term,
    fwd: &mut HashMap<String, String>, // formula var -> other var
    rev: &mut HashMap<String, String>, // other var -> formula var
) -> bool {
    match (formula, other) {
        (Term::Var(v1), Term::Var(v2)) => {
            if let Some(mapped) = fwd.get(v1) {
                return mapped == v2;
            }
            if let Some(mapped_back) = rev.get(v2) {
                return mapped_back == v1;
            }
            fwd.insert(v1.clone(), v2.clone());
            rev.insert(v2.clone(), v1.clone());
            true
        }

        (Term::Var(_), Term::Fun(_, _)) => false,
        (Term::Fun(_, _), Term::Var(_)) => false,

        (Term::Fun(f1, a1), Term::Fun(f2, a2)) => {
            if f1 != f2 || a1.len() != a2.len() {
                return false;
            }
            for (t1, t2) in a1.iter().zip(a2.iter()) {
                if !match_terms_alpha(t1, t2, fwd, rev) {
                    return false;
                }
            }
            true
        }
    }
}

/// Checks whether two formulas match modulo variable renaming (alpha-equivalence),
/// including quantified variables at the top level.
pub fn formulas_match_with_permutations(formula: &str, other_formula: &str) -> bool {
    let quant_re = Regex::new(r"!\s*\[([^\]]*)\]\s*:\s*(.*)").unwrap();

    let (vars, body) = if let Some(cap) = quant_re.captures(formula) {
        let vars: Vec<String> = cap[1].split(',').map(|v| v.trim().to_string()).collect();
        (vars, cap[2].trim().to_string())
    } else {
        (Vec::new(), formula.to_string())
    };

    // normalize other_formula once (includes quantifier handling and X-var renaming)
    let other_norm = normalize_formula_alpha(other_formula);

    let (other_lhs, other_rhs) = match parse_equation(&other_norm) {
        Some(x) => x,
        None => return false,
    };
    let parsed_other = Term::Fun("=".to_string(), vec![other_lhs, other_rhs]);

    if vars.len() <= 3 {
        // try all permutations for small number of quantified variables
        for perm in vars.iter().permutations(vars.len()).unique() {
            let mut body_perm = body.clone();
            for (i, var) in perm.iter().enumerate() {
                let canon_var = format!("V{}", i);
                let var_re = Regex::new(&format!(r"\b{}\b", regex::escape(var))).unwrap();
                body_perm = var_re
                    .replace_all(&body_perm, canon_var.as_str())
                    .to_string();
            }

            let norm_body = normalize_formula_alpha(&body_perm);

            let (lhs, rhs) = match parse_equation(&norm_body) {
                Some(x) => x,
                None => continue,
            };
            for (a, b) in [(lhs.clone(), rhs.clone()), (rhs, lhs)] {
                let parsed_formula = Term::Fun("=".to_string(), vec![a, b]);
                let mut fwd: HashMap<String, String> = HashMap::new();
                let mut rev: HashMap<String, String> = HashMap::new();
                if match_terms_alpha(&parsed_formula, &parsed_other, &mut fwd, &mut rev) {
                    return true;
                }
            }
        }
        false
    } else {
        // for larger formulas, just normalize in order without permutations
        let norm_body = normalize_formula_alpha(&body);

        let (lhs, rhs) = match parse_equation(&norm_body) {
            Some(x) => x,
            None => return false,
        };
        for (a, b) in [(lhs.clone(), rhs.clone()), (rhs, lhs)] {
            let parsed_formula = Term::Fun("=".to_string(), vec![a, b]);
            let mut fwd: HashMap<String, String> = HashMap::new();
            let mut rev: HashMap<String, String> = HashMap::new();
            if match_terms_alpha(&parsed_formula, &parsed_other, &mut fwd, &mut rev) {
                return true;
            }
        }
        false
    }
}
