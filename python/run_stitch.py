#!/usr/bin/env python3
"""
run_stitch.py: Run Stitch compression on big-step lemma terms and generate
abstracted TPTP problem files.

Stitch is run on the conjecture bodies of the big-step lemma files, so the
patterns it discovers are subterm shapes that recur across the things we are
actually trying to prove.  A pattern is only applied to a lemma when it
matches at least TWO positions in that formula, ensuring the resulting
statement is logically weaker than the original (the original is an instance
obtained by substituting the variable back).

Output directories:
  <output_dir>/abstracted_stitch_<i>/  — pattern i alone (≥2 occurrences)
  <output_dir>/abstracted_stitch_combined/ — all applicable patterns at once

Usage:
    python run_stitch.py <big_step_dir> <output_dir>
                        [--k K] [--max-arity N] [--iterations I]
"""

import sys
import re
import argparse
from collections import Counter
from pathlib import Path

from stitch_core import compress


# ============================================================
# Term parsing utilities (adapted from Abstractions.py)
# ============================================================

_HASH_RE = re.compile(r'#(\d+)$')
_DEBRUIJN_RE = re.compile(r'\$(\d+)$')


def parse_fof_term(term: str):
    """Parse a FOF prefix term like op(X0, X1) into a nested list."""
    stack = []
    current = []
    token = ''
    for char in term:
        if char == '(':
            if token:
                stack.append((current, token.strip()))
                current = []
                token = ''
        elif char == ')':
            if token.strip():
                current.append(token.strip())
                token = ''
            prev, func = stack.pop()
            prev.append([func] + current)
            current = prev
        elif char == ',':
            if token.strip():
                current.append(token.strip())
                token = ''
        else:
            token += char
    if token.strip():
        current.append(token.strip())
    return current[0] if current else token.strip()


def to_fof(tree) -> str:
    """Convert nested list back to FOF prefix form."""
    if isinstance(tree, str):
        return tree
    func = tree[0]
    args = ', '.join(to_fof(arg) for arg in tree[1:])
    return f"{func}({args})"


def to_lisp(tree) -> str:
    """Convert parsed FOF term to lisp-style expression."""
    if isinstance(tree, str):
        return tree
    return '(' + ' '.join(to_lisp(x) for x in tree) + ')'


def get_vars_in_term(term: str) -> list:
    """Extract single-uppercase-letter variables from a term."""
    return sorted(set(re.findall(r'\b[A-Z]\b', term)))


def convert_variables(expr: str, bound_vars: list) -> str:
    """Replace single-uppercase variable names with De Bruijn indices."""
    def replace_var(token: str) -> str:
        if re.fullmatch(r'[A-Z]', token):
            if token in bound_vars:
                index = len(bound_vars) - 1 - bound_vars[::-1].index(token)
                return f"${index}"
            raise ValueError(f"Unbound variable: {token}")
        return token

    tokens = re.findall(r'\(|\)|[^\s()]+', expr)
    new_tokens = [replace_var(tok) if tok not in '()' else tok for tok in tokens]
    return ''.join(
        f' {tok}' if tok not in ')' and i > 0 and tokens[i-1] != '(' else tok
        for i, tok in enumerate(new_tokens)
    )


def wrap_with_lambdas(expr: str, var_count: int) -> str:
    if var_count == 0:
        var_count = 1
    return "(lam " * var_count + f"{expr}" + ")" * var_count


def fof_to_lambda(term: str) -> str:
    """Embed first-order term into closed lambda term for Stitch."""
    vars_in_term = get_vars_in_term(term)
    tree = parse_fof_term(term)
    lisp_expr = to_lisp(tree)
    lisp_expr_with_indices = convert_variables(lisp_expr, vars_in_term)
    return wrap_with_lambdas(lisp_expr_with_indices, len(vars_in_term))


def parse_lisp_body(expr: str):
    """Parse lisp-style body to nested list."""
    tokens = re.findall(r'\(|\)|[^\s()]+', expr)
    stack = []
    current = []
    for tok in tokens:
        if tok == '(':
            stack.append(current)
            current = []
        elif tok == ')':
            last = current
            current = stack.pop()
            current.append(last)
        else:
            current.append(tok)
    return current[0] if current else []


def hash_to_var(index: int) -> str:
    if 0 <= index < 26:
        return chr(ord('A') + index)
    raise ValueError(f"Too many variables: index {index}")


def index_to_var(index: int, offset: int) -> str:
    j = offset + index
    if 0 <= j < 26:
        return chr(ord('A') + j)
    raise ValueError(f"Too many variables: offset {offset}, index {index}")


def collect_hash_indices(tree) -> set:
    if isinstance(tree, str):
        m = _HASH_RE.fullmatch(tree)
        return {int(m.group(1))} if m else set()
    out = set()
    for x in tree:
        out |= collect_hash_indices(x)
    return out


def convert_hashes_to_vars(tree, hash_index_set: set):
    if isinstance(tree, str):
        m = _HASH_RE.fullmatch(tree)
        if m:
            return hash_to_var(int(m.group(1)))
        return tree
    return [convert_hashes_to_vars(x, hash_index_set) for x in tree]


def convert_debruijn_to_vars(tree, offset: int):
    if isinstance(tree, str):
        m = _DEBRUIJN_RE.fullmatch(tree)
        if m:
            return index_to_var(int(m.group(1)), offset=offset)
        return tree
    return [convert_debruijn_to_vars(x, offset) for x in tree]


def remove_lambdas(tree):
    if isinstance(tree, str):
        return tree
    if tree and tree[0] == 'lam':
        return remove_lambdas(tree[1])
    return [remove_lambdas(x) for x in tree]


def derive_arities(terms: list) -> dict:
    arities = {}

    def traverse(tree):
        if isinstance(tree, str):
            return
        func = tree[0]
        if func not in arities:
            arities[func] = len(tree) - 1
        for arg in tree[1:]:
            traverse(arg)

    for term in terms:
        try:
            traverse(parse_fof_term(term))
        except Exception:
            pass
    return arities


def uncurry(tree, arities: dict):
    used_vars = get_vars_in_term(to_fof(tree))
    if not used_vars:
        used_vars = [chr(ord('A') - 1)]
    if isinstance(tree, list) and tree[0] in arities:
        arity = arities[tree[0]]
        diff = arity - (len(tree) - 1)
        if diff > 0:
            for i in range(diff):
                tree.append(chr(ord(used_vars[-1]) + i + 1))
    return tree


def fo_abstraction_from(abstraction, arities: dict) -> str:
    """Convert a Stitch abstraction to a FOF equation string."""
    lisp_expr = abstraction.body
    name = abstraction.name
    tree = parse_lisp_body(lisp_expr)
    hash_indices = collect_hash_indices(tree)
    tree = convert_hashes_to_vars(tree, hash_indices)
    offset = 1 + max(hash_indices) if hash_indices else 0
    tree = convert_debruijn_to_vars(tree, offset=offset)
    tree = remove_lambdas(tree)
    tree = uncurry(tree, arities)
    body = to_fof(tree)
    vars_ = get_vars_in_term(body)
    if vars_:
        decl = f"{name}({', '.join(vars_)})"
    else:
        decl = name
    return f"{decl} = {body}"


# ============================================================
# Proof term extraction
# ============================================================

def split_top_level_eq(s: str) -> list:
    """Split string on '=' at depth 0 (not inside parentheses)."""
    depth = 0
    for i, c in enumerate(s):
        if c == '(':
            depth += 1
        elif c == ')':
            depth -= 1
        elif c == '=' and depth == 0:
            return [s[:i].strip(), s[i+1:].strip()]
    return [s]


def extract_terms_from_proof(proof_file: str) -> list:
    """
    Extract both sides of equations from a redirected Vampire proof.
    Lines have the form: N. ! [X0,...] : lhs = rhs [rule ...]
    """
    terms = []
    # Match everything between the quantifier (if present) and the first '['
    line_re = re.compile(r'^\d+\.\s*(?:!\s*\[[^\]]*\]\s*:\s*)?(.*?)\s*\[')
    for line in Path(proof_file).read_text().splitlines():
        line = line.strip()
        if not line or line.startswith('%'):
            continue
        m = line_re.match(line)
        if not m:
            continue
        eq_str = m.group(1).strip()
        if not eq_str:
            continue
        parts = split_top_level_eq(eq_str)
        if len(parts) == 2:
            lhs, rhs = parts
            if lhs:
                terms.append(lhs)
            if rhs:
                terms.append(rhs)
    return terms


# ============================================================
# Lemma term extraction (primary Stitch corpus source)
# ============================================================

def collect_subterms(tree, acc: list) -> None:
    """Recursively append every compound subterm (depth ≥ 1) to acc."""
    if isinstance(tree, str):
        return
    acc.append(to_fof(tree))
    for child in tree[1:]:
        collect_subterms(child, acc)


def extract_terms_from_lemmas(big_step_dir: str) -> list:
    """
    Extract terms from the conjecture bodies of all big-step lemma files.
    Both sides of each equation are added, together with all their compound
    subterms, to give Stitch a rich corpus drawn directly from what we are
    trying to prove.
    """
    terms = []
    for p in sorted(Path(big_step_dir).glob("big_step_lemma_*.p")):
        parsed = parse_conjecture_block(p.read_text())
        if parsed is None:
            continue
        _, _, body = parsed
        for side in split_top_level_eq(body):
            side = side.strip()
            if not side:
                continue
            terms.append(side)
            try:
                collect_subterms(parse_fof_term(side), terms)
            except Exception:
                pass
    return terms


# ============================================================
# Variable renaming (Xn <-> single letters)
# ============================================================

def build_xn_mapping(terms: list) -> tuple:
    """Build X0->A, X1->B, ... mapping based on all Xn variables in terms."""
    all_vars: set = set()
    for t in terms:
        all_vars.update(re.findall(r'\bX\d+\b', t))
    sorted_vars = sorted(all_vars, key=lambda v: int(v[1:]))[:26]
    fwd = {v: chr(ord('A') + i) for i, v in enumerate(sorted_vars)}
    rev = {chr(ord('A') + i): v for i, v in enumerate(sorted_vars)}
    return fwd, rev


def rename_xn_to_letters(term: str, fwd: dict) -> str:
    """Replace Xn with single uppercase letters."""
    result = term
    # Sort by length descending to avoid partial matches (X10 before X1)
    for old, new in sorted(fwd.items(), key=lambda x: -len(x[0])):
        result = re.sub(r'\b' + re.escape(old) + r'\b', new, result)
    return result


def rename_letters_to_xn(term: str, rev: dict) -> str:
    """Replace single uppercase letters back to Xn, avoiding Y0."""
    result = term
    for old_letter, xn in sorted(rev.items(), reverse=True):
        result = re.sub(r'\b' + re.escape(old_letter) + r'\b', xn, result)
    return result


# ============================================================
# Pattern matching and substitution
# ============================================================

def match_term(tree, pattern, bindings: dict) -> bool:
    """
    One-way matching: single uppercase letters in pattern are pattern variables
    that can match any subterm. Other symbols must match exactly.
    """
    if isinstance(pattern, str):
        if re.fullmatch(r'[A-Z]', pattern):
            # Pattern variable: bind or check consistency
            if pattern in bindings:
                return to_fof(bindings[pattern]) == to_fof(tree)
            bindings[pattern] = tree
            return True
        # Constant or Xn variable — must match exactly
        return isinstance(tree, str) and tree == pattern
    if isinstance(tree, str):
        return False
    if tree[0] != pattern[0] or len(tree) != len(pattern):
        return False
    for t_child, p_child in zip(tree[1:], pattern[1:]):
        if not match_term(t_child, p_child, bindings):
            return False
    return True


def collect_matching_subterms(tree, pattern, acc: list) -> None:
    """
    Collect the FOF string of every subterm that matches pattern (outermost-first).
    Matching is structural: once a subtree matches, its children are not visited.
    """
    if match_term(tree, pattern, {}):
        acc.append(to_fof(tree))
        return          # outermost-first: don't descend into a matched subtree
    if isinstance(tree, str):
        return
    for child in tree[1:]:
        collect_matching_subterms(child, pattern, acc)


def replace_literal_subterm(tree, target_fof: str, replacement: str):
    """
    Replace every subtree whose to_fof() equals target_fof with replacement.
    Returns (new_tree, count).
    """
    if to_fof(tree) == target_fof:
        return replacement, 1
    if isinstance(tree, str):
        return tree, 0
    new_children = []
    total = 0
    for child in tree[1:]:
        new_child, n = replace_literal_subterm(child, target_fof, replacement)
        new_children.append(new_child)
        total += n
    return [tree[0]] + new_children, total


def apply_pattern_to_formula(formula_body: str, pattern_tree, fwd: dict, rev: dict,
                              replacement_var: str = 'Y0'):
    """
    Apply an abstraction pattern to a formula body (equation string, no quantifier).
    Renames Xn→letters, matches pattern, renames back.

    Sound generalisation strategy (mirrors the OCaml heuristic, extended to
    richer Stitch patterns):
      1. Collect every subterm (on both sides) that structurally matches the
         pattern.
      2. Group by the concrete FOF string of the matched subterm.
      3. Find the group with the highest count (must be ≥ 2).
      4. Replace every occurrence of that ONE specific subterm with
         replacement_var.

    Because we replace a single concrete subterm at all its positions, the
    original formula is an instance of the abstracted one (substitute
    replacement_var = that subterm), guaranteeing the abstracted statement is
    logically weaker.

    Returns the new formula string, or None if no subterm appears ≥ 2 times.
    """
    renamed = rename_xn_to_letters(formula_body, fwd)
    parts = split_top_level_eq(renamed)
    if len(parts) != 2:
        return None
    lhs_str, rhs_str = parts

    try:
        lhs_tree = parse_fof_term(lhs_str)
        rhs_tree = parse_fof_term(rhs_str)
    except Exception:
        return None

    # Collect all matched subterms across both sides
    matched: list = []
    collect_matching_subterms(lhs_tree, pattern_tree, matched)
    collect_matching_subterms(rhs_tree, pattern_tree, matched)

    if not matched:
        return None

    # Count occurrences of each distinct concrete subterm
    counts = Counter(matched)
    target_fof, best_count = counts.most_common(1)[0]
    if best_count < 2:
        return None

    # Replace all occurrences of that specific subterm
    new_lhs, n_lhs = replace_literal_subterm(lhs_tree, target_fof, replacement_var)
    new_rhs, n_rhs = replace_literal_subterm(rhs_tree, target_fof, replacement_var)

    new_lhs_str = to_fof(new_lhs)
    new_rhs_str = to_fof(new_rhs)

    # Degenerate: both sides collapsed to the same expression (e.g. Y0 = Y0)
    if new_lhs_str == new_rhs_str:
        return None

    return rename_letters_to_xn(f"{new_lhs_str} = {new_rhs_str}", rev)


# ============================================================
# TPTP file parsing and writing
# ============================================================

def strip_outer_parens(s: str) -> str:
    """Strip outer parentheses if they wrap the entire expression."""
    s = s.strip()
    if not s.startswith('('):
        return s
    depth = 0
    for i, c in enumerate(s):
        if c == '(':
            depth += 1
        elif c == ')':
            depth -= 1
        if depth == 0:
            if i == len(s) - 1:
                return s[1:-1].strip()
            return s
    return s


def parse_conjecture_block(content: str):
    """
    Parse the conjecture block from a TPTP file.
    Returns (tptp_name, vars_list, body_str) or None.
    The body_str is the bare equation without outer parens or quantifier.
    """
    lines = content.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        m = re.match(r'fof\s*\((\w+)\s*,\s*conjecture\s*,', line)
        if m:
            tptp_name = m.group(1)
            # Collect block until ")."
            block_lines = [line]
            j = i + 1
            while j < len(lines):
                stripped = lines[j].strip()
                block_lines.append(stripped)
                if stripped.endswith(').'):
                    break
                j += 1

            block = ' '.join(block_lines)

            # Extract formula: everything after ", conjecture," and before final ")."
            start_idx = block.index(', conjecture,') + len(', conjecture,')
            formula_str = block[start_idx:].strip()
            if formula_str.endswith(').'):
                formula_str = formula_str[:-2].strip()

            # Parse quantifier
            qm = re.match(r'!\s*\[([^\]]*)\]\s*:\s*(.*)', formula_str, re.DOTALL)
            if qm:
                vars_str = qm.group(1)
                vars_list = [v.strip() for v in vars_str.split(',') if v.strip()]
                body = strip_outer_parens(qm.group(2).strip())
                return tptp_name, vars_list, body
            else:
                body = strip_outer_parens(formula_str)
                return tptp_name, [], body
        i += 1
    return None


def replace_conjecture_in_file(content: str, tptp_name: str,
                                new_vars: list, new_body: str) -> str:
    """Replace the conjecture block in content with a new one."""
    lines = content.splitlines(keepends=True)
    result = []
    in_conjecture = False

    for line in lines:
        stripped = line.strip()
        if not in_conjecture:
            if re.match(r'fof\s*\(' + re.escape(tptp_name) + r'\s*,\s*conjecture\s*,',
                        stripped):
                in_conjecture = True
                continue
            result.append(line)
        else:
            if stripped.endswith(').'):
                in_conjecture = False
            continue  # Skip all lines of the old conjecture block

    # Build new conjecture block matching OCaml format
    if new_vars:
        vars_str = ', '.join(new_vars)
        new_block = (f"fof({tptp_name}, conjecture,\n"
                     f"    ! [{vars_str}] :\n"
                     f"      ({new_body})\n"
                     f").\n")
    else:
        new_block = (f"fof({tptp_name}, conjecture,\n"
                     f"    ({new_body})\n"
                     f").\n")

    return ''.join(result).rstrip() + '\n\n' + new_block


# ============================================================
# Abstraction filtering
# ============================================================

def extract_pattern_tree(fo_abstraction: str):
    """
    From 'fn_0(A, B) = op(A, op(A, B))', extract and return the RHS pattern tree.
    Returns None if the abstraction is invalid or higher-order.
    """
    # Higher-order check: contains 'lam'
    if 'lam' in fo_abstraction:
        return None
    parts = split_top_level_eq(fo_abstraction)
    if len(parts) != 2:
        return None
    pattern_str = parts[1].strip()
    if not pattern_str:
        return None
    try:
        tree = parse_fof_term(pattern_str)
    except Exception:
        return None
    # Trivial: pattern is just a single variable (no compression value)
    if isinstance(tree, str):
        return None
    return tree


# ============================================================
# Main
# ============================================================

def abstract_single_lemma(content: str, max_arity: int, iterations: int):
    """
    Run Stitch on the subterms of a single lemma's conjecture body.

    Returns (new_content, pattern_str) if a useful abstraction is found,
    or None if no ≥2-occurrence pattern exists within this lemma.
    """
    parsed = parse_conjecture_block(content)
    if parsed is None:
        return None
    tptp_name, orig_vars, body = parsed

    sides = [side.strip() for side in split_top_level_eq(body) if side.strip()]
    if len(sides) != 2:
        return None
    lhs, rhs = sides

    # Collect immediate subterms (direct children of each side's top-level symbol),
    # excluding any term string-equal to the full LHS or RHS.
    # This prevents Stitch from abstracting a whole side to Y0
    # (which produces unprovable fixed-point statements like Y0 = t(Y0, ...)).
    # Stitch inspects deeper structure itself during abstraction.
    excluded = {lhs, rhs}
    terms = []
    for side in sides:
        try:
            tree = parse_fof_term(side)
        except Exception:
            continue
        if isinstance(tree, str):
            continue
        for child in tree[1:]:
            child_fof = to_fof(child)
            if '(' in child_fof and child_fof not in excluded:
                terms.append(child_fof)
    terms = list(dict.fromkeys(terms))

    if not terms:
        return None

    # Build variable renaming (Xn -> single letters) scoped to this lemma
    fwd, rev = build_xn_mapping(terms)
    renamed = list(dict.fromkeys(rename_xn_to_letters(t, fwd) for t in terms if '(' in t))
    if not renamed:
        return None

    arities = derive_arities(renamed)

    try:
        lambda_terms = [fof_to_lambda(t) for t in renamed]
        result = compress(lambda_terms, iterations=iterations, max_arity=max_arity)
    except Exception:
        return None

    for abstraction in result.abstractions:
        try:
            fo_abs = fo_abstraction_from(abstraction, arities)
        except Exception:
            continue

        pattern_tree = extract_pattern_tree(fo_abs)
        if pattern_tree is None:
            continue

        new_body = apply_pattern_to_formula(body, pattern_tree, fwd, rev)
        if new_body is None:
            continue

        # Reject if a whole side collapsed to a bare variable (e.g. "Y0 = t(Y0,...)")
        # — means the entire LHS or RHS was abstracted away, producing an unprovable
        # fixed-point statement.
        new_sides = split_top_level_eq(new_body)
        if len(new_sides) == 2 and any('(' not in s.strip() for s in new_sides):
            continue

        new_vars = orig_vars + ['Y0'] if 'Y0' not in orig_vars else orig_vars
        new_content = replace_conjecture_in_file(content, tptp_name, new_vars, new_body)
        return new_content, to_fof(pattern_tree)

    return None


def main():
    parser = argparse.ArgumentParser(
        description='Run per-lemma Stitch abstraction and generate abstracted TPTP files')
    parser.add_argument('big_step_dir', help='Directory containing big-step lemma .p files')
    parser.add_argument('output_dir', help='Parent directory for abstracted_stitch/ subdir')
    parser.add_argument('--max-arity', type=int, default=3,
                        help='Max arity for Stitch (default: 3)')
    parser.add_argument('--iterations', type=int, default=3,
                        help='Stitch iterations (default: 3)')
    args = parser.parse_args()

    big_step_dir = Path(args.big_step_dir)
    output_dir = Path(args.output_dir)

    if not big_step_dir.exists():
        print(f"[WARN] Big-step directory not found: {big_step_dir}", file=sys.stderr)
        sys.exit(0)

    big_step_files = sorted(big_step_dir.glob("big_step_lemma_*.p"))
    if not big_step_files:
        print(f"[WARN] No big-step lemma files in {big_step_dir}", file=sys.stderr)
        sys.exit(0)

    mode_name = "abstracted_stitch"
    mode_dir = output_dir / mode_name
    import shutil
    if mode_dir.exists():
        shutil.rmtree(mode_dir)
    mode_dir.mkdir(parents=True, exist_ok=True)

    generated = 0
    skipped = 0

    for lemma_file in big_step_files:
        m = re.search(r'big_step_lemma_(\d{4})\.p$', lemma_file.name)
        if not m:
            continue
        lemma_num_str = m.group(1)

        content = lemma_file.read_text()
        result = abstract_single_lemma(content, args.max_arity, args.iterations)

        if result is None:
            skipped += 1
            continue

        new_content, pattern_str = result
        out_name = f"abstracted_stitch_lemma_{lemma_num_str}.p"
        (mode_dir / out_name).write_text(new_content)
        print(f"[INFO] lemma_{lemma_num_str}: abstracted via {pattern_str}", file=sys.stderr)
        generated += 1

    print(f"[INFO] abstracted_stitch: {generated} generated, {skipped} skipped.",
          file=sys.stderr)


if __name__ == '__main__':
    main()
