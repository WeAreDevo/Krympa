#!/usr/bin/env python3
"""
demo_stitch.py: Step-by-step illustration of the Stitch abstraction pipeline.

Walks through a small equational proof, showing at each stage:
  1. The redirected Vampire proof lines
  2. The equation terms extracted from the proof
  3. Variable renaming (Xn -> single letters) for Stitch
  4. The lambda-calculus embedding fed to Stitch
  5. The raw Stitch abstractions discovered
  6. Back-translation to first-order terms
  7. Pattern application to each big-step lemma conjecture
  8. The content of one generated abstracted_stitch file

Run:
    python demo_stitch.py              # uses built-in example
    python demo_stitch.py <proof.out>  # uses a real proof file + any big-step lemma dir
"""

import sys
import re
import tempfile
import textwrap
from pathlib import Path

from stitch_core import compress

# Pull in helpers from run_stitch.py (same directory)
sys.path.insert(0, str(Path(__file__).parent))
from run_stitch import (
    extract_terms_from_proof,
    extract_terms_from_lemmas,
    collect_subterms,
    build_xn_mapping,
    rename_xn_to_letters,
    fof_to_lambda,
    derive_arities,
    fo_abstraction_from,
    extract_pattern_tree,
    parse_conjecture_block,
    replace_conjecture_in_file,
    apply_pattern_to_formula,
    collect_matching_subterms,
    replace_literal_subterm,
    split_top_level_eq,
    rename_letters_to_xn,
    to_fof,
    parse_fof_term,
)

SEP  = "=" * 70
SEP2 = "-" * 70

# ---------------------------------------------------------------------------
# Example data
# ---------------------------------------------------------------------------

# A short redirected-Vampire proof for a magma satisfying  op(X, op(X, op(X, Y))) = X.
# Format produced by proof_turnaround.rs:
#   N. ! [X0, ...] : lhs = rhs [rule parents]
EXAMPLE_PROOF = """\
1. ! [X0,X1] : op(X0,op(X0,op(X0,X1))) = X0 [input]
2. ! [X0,X1] : op(X0,op(X0,op(X0,op(X0,X1)))) = op(X0,X1) [superposition 1,1]
3. ! [X0,X1] : op(X0,op(X0,X1)) = op(X0,op(X0,op(X0,op(X0,X1)))) [superposition 2,1]
4. ! [X0,X1] : op(X0,op(X0,X1)) = op(X0,X1) [demodulation 3,2]
5. ! [X0] : op(X0,X0) = X0 [superposition 4,4]
6. ! [X0,X1] : op(op(X0,X1),op(X0,X1)) = op(X0,X1) [superposition 5,5]
7. ! [X0,X1,X2] : op(op(X0,X1),op(op(X0,X1),X2)) = op(X0,X1) [superposition 4,4]
8. ! [X0,X1,X2] : op(X0,op(X1,op(X0,op(X1,X2)))) = op(X0,op(X1,X2)) [superposition 4,7]
"""

# Big-step lemma files: each is a TPTP .p file with the same axiom set
# and a single conjecture. These are created temporarily for the demo.
# (In the real pipeline these are produced by the OCaml parser.)
AXIOMS = """\
fof(a1, axiom,
    ! [X0, X1] :
      (op(X0,op(X0,op(X0,X1))) = X0)
).
"""

LEMMAS = {
    # Stitch corpus: feeds the self-application term op(X0,X0) into the corpus.
    "0001": "op(X0,op(X0,X1)) = op(X0,X1)",              # absorption
    "0002": "op(X0,X0) = X0",                             # idempotence (supplies op(A,A) to corpus)
    # Stitch match: op(C,C) pattern hits op(X0,X0) at 3 positions (2 inside LHS, 1 as RHS).
    # Abstracted: op(Y0,op(Y0,X1)) = Y0   [Y0 := op(X0,X0)]
    "0003": "op(op(X0,X0),op(op(X0,X0),X1)) = op(X0,X0)",
    # Stitch does NOT match here: op(C,C) hits the whole LHS op(op(A,B),op(A,B)) as one
    # occurrence, and RHS op(A,B) fails (A≠B), so only 1 occurrence total.
    "0004": "op(op(X0,X1),op(X0,X1)) = op(X0,X1)",
    # Stitch match: op(C,C) hits op(X0,X0) at 4 positions (3 inside LHS, 1 as RHS).
    # Abstracted: op(Y0,op(Y0,op(Y0,X1))) = Y0   [Y0 := op(X0,X0)]
    "0005": "op(op(X0,X0),op(op(X0,X0),op(op(X0,X0),X1))) = op(X0,X0)",
}


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def section(title):
    print(f"\n{SEP}")
    print(f"  {title}")
    print(SEP)


def subsection(title):
    print(f"\n{SEP2}")
    print(f"  {title}")
    print(SEP2)


def indent(text, n=4):
    return textwrap.indent(str(text), " " * n)


def build_lemma_file(num_str, body):
    """Return the content of a big-step lemma .p file."""
    vars_found = sorted(set(re.findall(r'\bX\d+\b', body)))
    vars_str = ", ".join(vars_found)
    quant = f"! [{vars_str}] :\n      " if vars_str else ""
    return (
        AXIOMS +
        f"\nfof(conjecture_{num_str}, conjecture,\n"
        f"    {quant}({body})\n"
        f").\n"
    )


# ---------------------------------------------------------------------------
# Main demo
# ---------------------------------------------------------------------------

def run_demo(proof_text, lemma_bodies):
    section("STEP 1 — Redirected Vampire proof")
    print(proof_text)

    # ------------------------------------------------------------------
    section("STEP 2 — Extract terms from lemma conjecture bodies")
    # Build temp big-step lemma files from the example data so we can use
    # extract_terms_from_lemmas (the new corpus source).
    import tempfile as _tf, os as _os
    tmp_dir = _tf.mkdtemp(prefix="demo_lemmas_")
    for num_str, body in lemma_bodies.items():
        Path(tmp_dir, f"big_step_lemma_{num_str}.p").write_text(
            build_lemma_file(num_str, body))

    all_terms = extract_terms_from_lemmas(tmp_dir)
    # also keep proof terms available for step 1 display (not used for Stitch)
    print(f"  Collected {len(all_terms)} terms (conjecture sides + all subterms):\n")
    unique = list(dict.fromkeys(all_terms))
    for t in unique:
        print(f"    {t}")

    # ------------------------------------------------------------------
    section("STEP 3 — Variable renaming  Xn -> single uppercase letters")
    fwd, rev = build_xn_mapping(unique)
    print(f"  Mapping:  {fwd}\n")
    compound = [rename_xn_to_letters(t, fwd) for t in unique if "(" in t]
    compound = list(dict.fromkeys(compound))
    print(f"  Renamed compound terms ({len(compound)} unique):\n")
    for t in compound:
        print(f"    {t}")

    # ------------------------------------------------------------------
    section("STEP 4 — Lambda-calculus embedding (input to Stitch)")
    print("  Each term t(x1,...,xk) becomes  (lam (lam ... body))  where\n"
          "  xi are replaced by De Bruijn indices $i.\n")
    for t in compound[:8]:          # show first 8 to keep output manageable
        lam = fof_to_lambda(t)
        print(f"    {t}")
        print(f"    -> {lam}\n")

    # ------------------------------------------------------------------
    section("STEP 5 — Run Stitch compression")
    arities = derive_arities(compound)
    print(f"  Function arities derived from terms: {arities}\n")
    lambda_terms = [fof_to_lambda(t) for t in compound]
    print(f"  Calling compress({len(lambda_terms)} lambda terms, iterations=3, max_arity=3) ...\n")
    result = compress(lambda_terms, iterations=3, max_arity=3)
    abstractions = result.abstractions
    print(f"  Stitch returned {len(abstractions)} abstraction(s).")

    # ------------------------------------------------------------------
    section("STEP 6 — Back-translate abstractions to first-order terms")
    patterns = []
    for i, abst in enumerate(abstractions[:5]):
        print(f"\n  [{i}] Stitch body (lambda term):  {abst.body}")
        try:
            fo = fo_abstraction_from(abst, arities)
        except Exception as e:
            print(f"       -> back-translation failed: {e}  (skipped)")
            continue

        print(f"       FOF equation:             {fo}")
        pattern = extract_pattern_tree(fo)
        if pattern is None:
            print(f"       -> filtered out (higher-order or trivial)")
            continue
        print(f"       Pattern tree (RHS):       {to_fof(pattern)}")
        patterns.append((i, pattern, fo))

    if not patterns:
        print("\n  No usable patterns found — nothing to abstract.")
        return

    # ------------------------------------------------------------------
    section("STEP 7 — Apply each pattern to lemma conjectures  (require ≥2 occurrences)")
    print("  Sound generalisation rule (mirrors the OCaml 'abstracted' mode):\n"
          "    1. Find every subterm structurally matching the pattern (outermost-first).\n"
          "    2. Group by the *exact FOF string* of the matched subterm.\n"
          "    3. The most frequent group must appear ≥ 2 times.\n"
          "    4. Replace every occurrence of that ONE specific subterm with Y0.\n"
          "\n"
          "  Why ≥2?\n"
          "    Replacing a single occurrence makes the statement *stronger* (universally\n"
          "    quantified over Y0 where only one specific value was needed) — it may be\n"
          "    false, and offers no proof-shortening benefit even when provable.\n"
          "    With ≥2 occurrences of the SAME concrete subterm, the original formula\n"
          "    is an instance of the abstracted one (substitute Y0 = that subterm), so\n"
          "    the abstracted is logically weaker, and the prover can treat Y0 as an\n"
          "    atom without unfolding its internal definition.\n"
          "\n"
          "  Why *same concrete subterm*?\n"
          "    Replacing two *different* matching subterms (e.g. op(X0,X0) and op(X1,X1))\n"
          "    with the same Y0 would assert they are equal — introducing a constraint not\n"
          "    in the original, potentially making the formula false.\n"
          "\n"
          "  Outermost-first matching ensures we don't double-count nested occurrences.\n"
          "  It also means purely-flat patterns (like op(A,B)) always consume the whole\n"
          "  term at the top level (1 occurrence each side), so they rarely trigger.\n"
          "  Patterns with equality constraints (like op(C,C)) can fail at a parent and\n"
          "  descend into children, finding the repeated inner subterm naturally.\n")

    for abs_idx, pattern, fo_abs in patterns:
        subsection(f"Abstraction {abs_idx}:  {to_fof(pattern)}")
        print(f"  Full equation:  {fo_abs}\n")

        hits = 0
        for num_str, body in lemma_bodies.items():
            new_body = apply_pattern_to_formula(body, pattern, fwd, rev)
            marker = "  >>>" if new_body else "     "
            print(f"{marker} lemma_{num_str}:  {body}")
            if new_body:
                print(f"       abstracted:  {new_body}")
                hits += 1

        print(f"\n  Total matches (≥2 occurrences): {hits} / {len(lemma_bodies)} lemmas")

    # ------------------------------------------------------------------
    section("STEP 8 — Sample generated .p file")

    # Pick the first pattern that actually matched at least one lemma
    sample_pattern_entry = None
    sample_num = None
    sample_new_body = None
    for entry in patterns:
        abs_idx, pattern, fo_abs = entry
        for num_str, body in lemma_bodies.items():
            new_body = apply_pattern_to_formula(body, pattern, fwd, rev)
            if new_body is not None:
                sample_pattern_entry = entry
                sample_num = num_str
                sample_new_body = new_body
                break
        if sample_pattern_entry is not None:
            break

    if sample_pattern_entry is None:
        print("  (no pattern matched any lemma)")
        return

    abs_idx, pattern, fo_abs = sample_pattern_entry
    mode_name = f"abstracted_stitch_{abs_idx}"

    original_content = build_lemma_file(sample_num, lemma_bodies[sample_num])
    parsed = parse_conjecture_block(original_content)
    tptp_name, orig_vars, _ = parsed
    new_vars = orig_vars + ["Y0"]
    new_content = replace_conjecture_in_file(
        original_content, tptp_name, new_vars, sample_new_body
    )

    filename = f"{mode_name}_lemma_{sample_num}.p"
    print(f"  File:  lemmas/{mode_name}/{filename}\n")
    print(f"  Original conjecture (big-step):")
    print(indent(f"! [{', '.join(orig_vars)}] : ({lemma_bodies[sample_num]})"))
    print(f"\n  Abstracted conjecture (abstracted_stitch_{abs_idx}):")
    print(indent(f"! [{', '.join(new_vars)}] : ({sample_new_body})"))
    print(f"\n  Full file contents:")
    print(SEP2)
    print(new_content)
    print(SEP2)

    print(f"\n  Interpretation: the prover must prove the conjecture for *all* Y0,\n"
          f"  not just Y0 = {to_fof(pattern)} (the specific abstracted subterm).\n"
          f"  If the axioms suffice for all Y0, the proof may be shorter because\n"
          f"  the internal structure of Y0 is irrelevant.\n")

    section("STEP 9 — Combined abstraction (all patterns simultaneously)")
    print("  Each lemma gets ONE file where every applicable pattern is applied\n"
          "  at once, using distinct variables Y0, Y1, ...  This produces the\n"
          "  most general (weakest) statement and goes in abstracted_stitch_combined/.\n")

    for num_str, body in lemma_bodies.items():
        current = rename_xn_to_letters(body, fwd)
        added_vars = []
        for abs_idx, pattern, _ in patterns:
            var_name = f'Y{abs_idx}'
            parts = split_top_level_eq(current)
            if len(parts) != 2:
                continue
            try:
                lhs_t = parse_fof_term(parts[0])
                rhs_t = parse_fof_term(parts[1])
            except Exception:
                continue
            from collections import Counter
            matched = []
            collect_matching_subterms(lhs_t, pattern, matched)
            collect_matching_subterms(rhs_t, pattern, matched)
            if not matched:
                continue
            counts = Counter(matched)
            target_fof, best_count = counts.most_common(1)[0]
            if best_count < 2:
                continue
            new_lhs, _ = replace_literal_subterm(lhs_t, target_fof, var_name)
            new_rhs, _ = replace_literal_subterm(rhs_t, target_fof, var_name)
            new_lhs_str = to_fof(new_lhs)
            new_rhs_str = to_fof(new_rhs)
            if new_lhs_str != new_rhs_str:
                current = f"{new_lhs_str} = {new_rhs_str}"
                added_vars.append(var_name)

        if added_vars:
            final = rename_letters_to_xn(current, rev)
            print(f"  lemma_{num_str}:")
            print(f"    original:   {body}")
            print(f"    combined:   {final}   [{', '.join(added_vars)}]\n")

    # Clean up temp dir
    import shutil
    shutil.rmtree(tmp_dir, ignore_errors=True)

    section("DONE")
    print(f"  In the full pipeline, Krympa runs Vampire and Twee on every generated")
    print(f"  .p file and records the shortest proof in summary.json, alongside the")
    print(f"  big-step / small-step / abstracted results.")
    print()


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    if len(sys.argv) >= 2:
        # Use a real proof file provided on the command line
        proof_file = Path(sys.argv[1])
        if not proof_file.exists():
            print(f"[ERROR] File not found: {proof_file}", file=sys.stderr)
            sys.exit(1)
        proof_text = proof_file.read_text()

        # If a big-step dir is also given, read lemmas from it
        if len(sys.argv) >= 3:
            big_step_dir = Path(sys.argv[2])
            lemma_bodies = {}
            for p in sorted(big_step_dir.glob("big_step_lemma_*.p")):
                m = re.search(r'big_step_lemma_(\d{4})\.p$', p.name)
                if not m:
                    continue
                parsed = parse_conjecture_block(p.read_text())
                if parsed:
                    lemma_bodies[m.group(1)] = parsed[2]
            if not lemma_bodies:
                print(f"[WARN] No big-step lemmas found in {big_step_dir}; "
                      f"using built-in example lemmas.", file=sys.stderr)
                lemma_bodies = LEMMAS
        else:
            lemma_bodies = LEMMAS
    else:
        # Built-in example
        proof_text = EXAMPLE_PROOF
        lemma_bodies = LEMMAS

    run_demo(proof_text, lemma_bodies)
