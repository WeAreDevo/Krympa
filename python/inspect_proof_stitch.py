#!/usr/bin/env python3
"""
inspect_proof_stitch.py

Reads a minimized Krympa proof output, extracts the local dependency DAG of
candidate lemmas, runs Stitch corpus-wide on those formulas, and shows what
abstracted lemma variants would look like.

Unlike the per-lemma mode in run_stitch.py, Stitch here sees all proof lemmas
at once — the natural setting for cross-lemma pattern discovery on the minimal
local corpus that was actually used in the final proof.

Usage:
    python python/inspect_proof_stitch.py [proof_file]
    python python/inspect_proof_stitch.py --skip-stitch [proof_file]
"""

import re
import sys
from collections import defaultdict
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_PROOF = REPO_ROOT / "output" / "proof_Equation650_implies_Equation448.out"

SEP  = "=" * 72
SEP2 = "-" * 72

LEMMA_NAME_RE = re.compile(r'\b([a-z][a-z_]*_\d{4})\b')


# ---------------------------------------------------------------------------
# Proof parsing
# ---------------------------------------------------------------------------

def parse_proof(path: Path):
    """
    Parse a Krympa proof output file.

    Returns:
        lemmas : dict[name -> formula_str]  ordered by appearance
        deps   : dict[name -> list[name]]   lemma-to-lemma edges only
    """
    lemmas = {}
    deps   = defaultdict(list)

    for line in path.read_text().splitlines():
        if not line.startswith('%'):
            continue
        # skip section headers
        if re.match(r'^%\s*===', line):
            continue

        # split at | deps: first, then extract name: formula
        if '| deps:' in line:
            body_part, deps_part = line.split('| deps:', 1)
        else:
            body_part, deps_part = line, ''

        # strip leading %
        body_part = body_part.lstrip('%').strip()

        # name: formula
        colon = body_part.index(':')
        name    = body_part[:colon].strip()
        formula = body_part[colon+1:].strip()

        if not name or not formula:
            continue

        lemmas[name] = formula

        for dep_name in LEMMA_NAME_RE.findall(deps_part):
            if dep_name != name and dep_name not in deps[name]:
                deps[name].append(dep_name)

    return lemmas, dict(deps)


# ---------------------------------------------------------------------------
# DAG display
# ---------------------------------------------------------------------------

def topo_sort(lemmas, deps):
    visited = set()
    order   = []

    def visit(n):
        if n in visited:
            return
        visited.add(n)
        for d in deps.get(n, []):
            if d in lemmas:
                visit(d)
        order.append(n)

    for n in lemmas:
        visit(n)
    return order


def print_dag(lemmas, deps):
    order  = topo_sort(lemmas, deps)
    name_w = max(len(n) for n in order)

    print(f"\n  {'lemma':<{name_w}}  deps")
    print(f"  {'-'*name_w}  {'-'*50}")
    for name in order:
        dep_str = ', '.join(deps.get(name, [])) or '(axioms only)'
        print(f"  {name:<{name_w}}  {dep_str}")


# ---------------------------------------------------------------------------
# Stitch corpus-wide discovery
# ---------------------------------------------------------------------------

def run_stitch_on_corpus(lemmas: dict, max_arity=3, iterations=3, k=5):
    """
    Run Stitch over all proof-lemma formulas at once.

    Returns list of (pattern_fof, [(lemma_name, abstracted_formula), ...]).
    """
    try:
        from stitch_core import compress
    except ImportError:
        print("  [ERROR] stitch_core not found — activate .venv first.", file=sys.stderr)
        return []

    sys.path.insert(0, str(REPO_ROOT / 'python'))
    import run_stitch as rs

    # Build corpus: encode every lemma body's compound subterms as lambda terms.
    # We also store per-lemma context (fwd/rev rename maps) for pattern application.
    per_lemma = []   # (name, formula, fwd, rev)
    all_lambda = []

    # Build a shared variable renaming from all Xn vars across all formulas
    all_bodies = list(lemmas.values())
    fwd, rev = rs.build_xn_mapping(all_bodies)

    for name, formula in lemmas.items():
        parts = rs.split_top_level_eq(formula)
        if len(parts) != 2:
            continue

        renamed = rs.rename_xn_to_letters(formula, fwd)
        renamed_parts = rs.split_top_level_eq(renamed)
        if len(renamed_parts) != 2:
            continue

        # Collect compound immediate subterms from both sides (same strategy as run_stitch.py)
        terms = []
        lhs, rhs = renamed_parts
        excluded = {lhs.strip(), rhs.strip()}
        for side in renamed_parts:
            try:
                tree = rs.parse_fof_term(side.strip())
            except Exception:
                continue
            if isinstance(tree, str):
                continue
            for child in tree[1:]:
                child_fof = rs.to_fof(child)
                if '(' in child_fof and child_fof not in excluded:
                    terms.append(child_fof)
        terms = list(dict.fromkeys(terms))

        if not terms:
            continue

        try:
            lambda_terms = [rs.fof_to_lambda(t) for t in terms]
        except Exception:
            continue

        all_lambda.extend(lambda_terms)
        per_lemma.append((name, formula, fwd, rev))

    if not per_lemma or not all_lambda:
        print("  [WARN] No encodable lemmas.", file=sys.stderr)
        return []

    print(f"  Corpus: {len(per_lemma)} lemmas, {len(all_lambda)} lambda terms total")

    # stitch_core has a known assertion bug that triggers at larger arities/corpora;
    # retry with progressively smaller parameters if needed.
    result = None
    for try_arity, try_iters in [(max_arity, iterations), (2, 2), (1, 1)]:
        try:
            result = compress(all_lambda, iterations=try_iters, max_arity=try_arity)
            print(f"  compress succeeded (max_arity={try_arity}, iterations={try_iters})")
            break
        except Exception as e:
            print(f"  [WARN] compress failed (max_arity={try_arity}, iterations={try_iters}): retrying…",
                  file=sys.stderr)
    if result is None:
        print("  [ERROR] stitch_core.compress failed at all parameter levels.", file=sys.stderr)
        return []

    output = []
    for abstraction in result.abstractions:
        try:
            fo_abs = rs.fo_abstraction_from(abstraction, {})
        except Exception:
            continue

        pattern_tree = rs.extract_pattern_tree(fo_abs)
        if pattern_tree is None:
            continue
        pattern_fof = rs.to_fof(pattern_tree)

        matches = []
        for name, formula, fwd_l, rev_l in per_lemma:
            new_body = rs.apply_pattern_to_formula(formula, pattern_tree, fwd_l, rev_l)
            if new_body is None:
                continue
            # reject if a whole side collapsed to a bare variable
            new_sides = rs.split_top_level_eq(new_body)
            if len(new_sides) == 2 and any('(' not in s.strip() for s in new_sides):
                continue
            matches.append((name, new_body))

        if matches:
            output.append((pattern_fof, matches))

    return output


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def section(title):
    print(f"\n{SEP}\n  {title}\n{SEP}")


def main():
    skip_stitch = '--skip-stitch' in sys.argv
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    proof_path = Path(args[0]).resolve() if args else DEFAULT_PROOF

    if not proof_path.exists():
        print(f"[ERROR] Not found: {proof_path}", file=sys.stderr)
        sys.exit(1)

    # ------------------------------------------------------------------
    section("STEP 1 — Parse proof and extract local dependency DAG")
    print(f"  File: {proof_path.name}\n")

    lemmas, deps = parse_proof(proof_path)
    print(f"  Lemmas in proof: {len(lemmas)}")
    print_dag(lemmas, deps)

    # ------------------------------------------------------------------
    section("STEP 2 — Formulas in topological order")
    order = topo_sort(lemmas, deps)
    for name in order:
        formula  = lemmas[name]
        dep_list = ', '.join(deps.get(name, [])) or 'axioms only'
        print(f"\n  {name}")
        print(f"    {formula}")
        print(f"    deps: {dep_list}")

    # ------------------------------------------------------------------
    section("STEP 3 — Stitch corpus-wide pattern discovery")

    if skip_stitch:
        print("  (--skip-stitch: skipped)")
        return

    patterns = run_stitch_on_corpus(lemmas, max_arity=3, iterations=3, k=5)

    if not patterns:
        print("  No compressive patterns found.")
        return

    print(f"\n  {len(patterns)} pattern(s) found:\n")
    for i, (pattern_fof, matches) in enumerate(patterns):
        print(f"  Pattern {i}: {pattern_fof}")
        print(f"  Applies to {len(matches)}/{len(lemmas)} lemmas in this proof:")
        for name, abstracted in matches:
            original = lemmas[name]
            print(f"\n    {name}")
            print(f"      original  : {original}")
            print(f"      abstracted: {abstracted}")
        print(f"\n  {SEP2}")


if __name__ == '__main__':
    main()
