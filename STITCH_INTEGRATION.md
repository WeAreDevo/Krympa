# Stitch Abstraction Integration

## Overview

This change integrates [Stitch](https://stitch-bindings.readthedocs.io/) into Krympa's `collect` phase to generate additional TPTP problem variants for each lemma. Alongside the existing `big-step`, `small-step`, and `abstracted` modes, Krympa now also produces `abstracted_stitch_N` and `abstracted_stitch_combined` variants driven by data-derived compression patterns discovered across the lemma corpus.

---

## Background: The Existing `abstracted` Mode

The existing OCaml heuristic (`ocaml/lib/lemma_extractor.ml`) abstracts a lemma by:

1. Scanning the conjecture body for flat subterms of the form `op(Xi, Xj)` where both arguments are variables.
2. Finding the one that appears **most frequently as the same literal string** (e.g., `op(X0, X1)` appearing at three positions in the formula).
3. Replacing every occurrence of that exact string with a fresh universally-quantified variable `Y0`.

**Example.** The lemma `op(op(X0,X1), op(op(X0,X1), X2)) = op(X0,X1)` contains `op(X0,X1)` three times. The OCaml heuristic replaces all three with `Y0`, giving: `op(Y0, op(Y0, X2)) = Y0`.

---

## Why the ≥2 Occurrence Requirement Is Semantically Necessary

This is the central soundness condition — it is not just a heuristic filter.

### What abstraction does logically

When you replace a subterm `t` with a fresh variable `Y0`, the resulting formula is universally quantified over `Y0`. The original formula is then a *specific instance* of the abstracted one — obtained by substituting `Y0 := t`. This means:

> **Abstracted provable ⟹ Original provable** (by instantiation).

So abstracting is always sound from an implication standpoint: if the prover proves the abstracted version, the original follows for free.

### Why single-occurrence abstraction is useless

If `t` appears only once in the formula, the abstracted statement replaces that single occurrence with `Y0` and quantifies universally over it. The claim is now "for all `Y0`, [formula]", which is **strictly stronger** than the original. This may be false even when the original is true:

```
Original:  op(X0, X1) = X0          (maybe true for specific X0, X1 in this algebra)
Abstracted: Y0 = X0                  (false for all Y0 — obviously unprovable)
```

Even when the abstracted statement happens to be provable, there is no proof-shortening benefit: there is no shared structure to exploit. The prover is doing strictly more work for no gain.

### Why ≥2 occurrences of the **same concrete subterm** enables shorter proofs

When the same concrete subterm `t` appears in **two or more positions**, the prover reasoning about the abstracted formula can treat `Y0` as an atomic unit — it never needs to unfold `Y0`'s internal definition. The shared occurrences are tied together by the single variable, so the proof can exploit their uniformity directly.

This is precisely what makes the OCaml abstraction useful: the prover sees `op(Y0, op(Y0, X2)) = Y0` and can reason about idempotence (`op(Y0, Y0) = Y0`) or absorption without ever considering what `Y0 = op(X0, X1)` is made of.

### Why "same concrete subterm" matters (the binding-consistency requirement)

It is not enough to count how many subterms *structurally match the pattern*. They must be the **same concrete subterm** (identical FOF string after renaming).

**Counter-example.** Suppose the pattern is `op(A, A)` (i.e., a term applied to itself) and the formula is:
```
op(op(X0,X1), op(X0,X1)) = op(op(X2,X3), op(X2,X3))
```
Both sides match the pattern — but `op(X0,X1)` and `op(X2,X3)` are *different* concrete subterms. Replacing both with `Y0` gives:
```
op(Y0, Y0) = op(Y0, Y0)   →   trivially Y0 = Y0
```
This destroys the information content of the lemma. Worse, if the formula were asymmetric, replacing two *different* subterms with the same variable introduces a new equality constraint between them that was not in the original formula — which may make the abstracted statement false.

**The algorithm therefore:**

1. Collects all structurally-matching subterms (outermost-first).
2. Groups them by their **exact FOF string** (same concrete term).
3. Picks the group with the highest count.
4. Proceeds only if that count is **≥ 2**.
5. Replaces every occurrence of **that one specific subterm** with `Y0`.

This mirrors exactly what the OCaml heuristic does — the only difference is that Stitch discovers which *structural patterns* are worth looking for, rather than restricting to flat `op(Xi, Xj)` applications.

---

## What Was Changed

### New file: `python/run_stitch.py`

A self-contained Python script that drives the full Stitch abstraction pipeline:

1. **Corpus extraction** — reads all `big_step_lemma_*.p` files and collects both sides of each conjecture body plus all compound subterms. Using lemma conjecture bodies (rather than proof-step equations) ensures the patterns Stitch finds are directly relevant to what we are trying to prove.

2. **Variable renaming** — renames `X0→A, X1→B, ...` because `stitch_core` requires single uppercase letters as variables.

3. **Lambda embedding** — each FOF term `f(x1,...,xk)` is embedded as a closed lambda term `(lam (lam ... body))` with De Bruijn indices. This is required input format for `stitch_core`.

4. **Stitch compression** — calls `stitch_core.compress(terms, iterations=3, max_arity=3)` to obtain up to `k=5` abstractions ordered by compression gain across the corpus.

5. **Back-translation** — converts each Stitch λ-abstraction back to a first-order FOF equation (hash/de Bruijn index substitution, lambda stripping, arity-based uncurrying).

6. **Filtering** — skips higher-order abstractions (containing `lam`) and trivial ones (a single variable).

7. **Pattern application** — for each usable pattern, applies it to every big-step lemma conjecture using the binding-consistency algorithm (≥2 same-concrete-subterm occurrences). Writes `abstracted_stitch_N/abstracted_stitch_N_lemma_NNNN.p`.

8. **Combined directory** — applies *all* applicable patterns simultaneously to each lemma, using distinct variables `Y0, Y1, ...` per pattern. Each pattern is applied with the same soundness check. Writes `abstracted_stitch_combined/abstracted_stitch_combined_lemma_NNNN.p`. This produces the most general (weakest) abstracted statement for each lemma.

Usage:
```
python run_stitch.py <big_step_dir> <output_dir> [--k 5] [--max-arity 3] [--iterations 3]
```

---

### Modified: `rust/src/core.rs`

**`collect()`** — after the existing OCaml parser loop, calls `run_stitch_script(proof_file, &lemmas_dir)`, which runs the Python script and returns the list of all generated `.p` file paths. These are appended to `all_lemma_files` before the `prove_lemmas` call, so Vampire and Twee run on stitch variants identically to the existing modes.

**`run_stitch_script()`** — private function that:
- Invokes `python3 ../python/run_stitch.py <lemmas_dir>/big-step <lemmas_dir>`
- After the script exits, scans `<lemmas_dir>/abstracted_stitch_*/` for `.p` files (covers both `abstracted_stitch_N/` and `abstracted_stitch_combined/`)
- Returns a sorted list of paths; returns an empty list on any error (fail-safe)

---

### Modified: `rust/src/utils.rs`

**`load_lemma()`** — the regex for recognising stitch lemma names is updated to accept both numeric and `combined` suffixes:
```rust
let re = Regex::new(r"^(abstracted_stitch_(?:\d+|combined))_lemma_\d+$").unwrap();
```

---

### Modified: `rust/src/minimize.rs`

**`proof_uses_lemma()`** — the stitch alternate regex pattern matches both forms:
```rust
let stitch_alt = format!(r"abstracted_stitch_(?:\d+|combined)_lemma_{}", num);
```

---

## Data Flow

```
big-step lemma files (conjecture bodies + subterms)
         │
         └─ run_stitch.py
               │   stitch_core.compress(lambda_terms)
               │
               ├─ abstracted_stitch_0/abstracted_stitch_0_lemma_NNNN.p
               ├─ abstracted_stitch_1/abstracted_stitch_1_lemma_NNNN.p
               │   ...
               └─ abstracted_stitch_combined/abstracted_stitch_combined_lemma_NNNN.p

All .p files → prove_lemmas (Vampire + Twee) → summary.json
summary.json → shorten → minimize
```

---

## Comparison with the OCaml `abstracted` Mode

| Property | OCaml `abstracted` | Stitch `abstracted_stitch_N` |
|---|---|---|
| Pattern shape | Flat `op(Xi, Xj)` only | Arbitrary depth, e.g. `op(X, op(X, Y))` |
| Pattern source | Hand-coded scan | Learned from cross-lemma corpus |
| Patterns per run | 1 | Up to `k` (default 5) |
| Selection criterion | Most frequent flat application | Maximum compression gain (Stitch objective) |
| Soundness check | Same string appears ≥ 2 times | Same concrete subterm appears ≥ 2 times |
| Combined variant | No | Yes (`abstracted_stitch_combined`) |

Both approaches share the same core soundness argument: replacing a single concrete subterm at all its positions with a fresh universal variable produces a logically weaker statement, whose proofs can be shorter because the prover need not reason about the subterm's internal structure.

---

## Files Changed

| File | Type | Change |
|---|---|---|
| `python/run_stitch.py` | New | Stitch runner and TPTP generator |
| `python/demo_stitch.py` | New | Step-by-step illustration of the pipeline |
| `rust/src/core.rs` | Modified | Add `run_stitch_script()`, call in `collect()` |
| `rust/src/utils.rs` | Modified | Add `abstracted_stitch_(?:\d+|combined)` case in `load_lemma()` |
| `rust/src/minimize.rs` | Modified | Update `proof_uses_lemma()` regex for combined |
| `ocaml/lib/lemma_extractor.ml` | Unchanged | — |
| `rust/Cargo.toml` | Unchanged | — |
