# Stitch Abstraction Integration

## Overview

This change integrates [Stitch](https://github.com/mlb2251/stitch) into Krympa's `collect` phase to generate a fourth lemma mode — **abstracted_stitch** — alongside the existing `big-step`, `small-step`, and `abstracted` modes. For each lemma, Stitch finds a structural pattern within that lemma's own conjecture body and replaces a repeated concrete subterm with a fresh universally-quantified variable, producing a logically weaker but more general statement. The resulting TPTP files are handed to the same Vampire + Twee pipeline as all other modes.

---

## Background: The Existing `abstracted` Mode

The OCaml heuristic (`ocaml/lib/lemma_extractor.ml`) abstracts a lemma by:

1. Scanning the conjecture body for flat subterms of the form `op(Xi, Xj)` where both arguments are variables.
2. Finding the one that appears **most frequently as the same literal string**.
3. Replacing every occurrence with a fresh universally-quantified variable `Y0`.

**Example.** `op(op(X0,X1), op(op(X0,X1), X2)) = op(X0,X1)` contains `op(X0,X1)` three times. After abstraction: `op(Y0, op(Y0, X2)) = Y0`.

The `abstracted_stitch` mode generalises this by discovering richer patterns (arbitrary depth, not just flat `op(Xi,Xj)`) using Stitch compression.

---

## Soundness: Why the ≥2 Occurrence Requirement Matters

Replacing a subterm `t` with a fresh variable `Y0` universally quantifies the result over `Y0`. The original formula is then a *specific instance* — obtained by substituting `Y0 := t`. Therefore:

> **Abstracted provable ⟹ Original provable** (by instantiation).

Abstraction is only sound — and only useful — when the **same concrete subterm** appears at **≥ 2 positions**:

- With a single occurrence, the abstracted statement is strictly stronger than the original and may be unprovable even when the original holds.
- With ≥ 2 occurrences of the *same concrete string*, the prover can treat `Y0` as an atomic unit. The shared positions are tied together by one variable, enabling the prover to exploit structural uniformity without unfolding `Y0`'s definition — which is precisely the source of proof shortening.

**Binding-consistency requirement.** Multiple structurally-matching subterms are not sufficient; they must be the same concrete FOF string. Replacing two different concrete subterms with the same variable would introduce a new equality constraint between them not present in the original, potentially making the abstracted statement false.

The algorithm:
1. Collects all subterms that structurally match the discovered pattern.
2. Groups them by exact FOF string.
3. Selects the group with the highest count.
4. Proceeds only if that count is ≥ 2.
5. Replaces every occurrence of that one concrete subterm with `Y0`.

---

## What Was Changed

### `python/run_stitch.py`

Drives per-lemma Stitch abstraction. For each `big_step_lemma_NNNN.p` file:

1. **Parse** the TPTP conjecture body into a prefix-term tree.
2. **Build corpus** from the *immediate subterms* of each side of the equation (one level below the root), excluding the full LHS and RHS. This prevents Stitch from abstracting an entire side of the equation, which would produce unprovable fixed-point statements like `Y0 = t(Y0, ...)`.
3. **Lambda-encode** each corpus term with De Bruijn indices (required by `stitch_core`).
4. **Compress** via `stitch_core.compress(terms, iterations=3, max_arity=3)`.
5. **Apply** each discovered pattern back to the original formula body using the binding-consistency algorithm.
6. **Reject** if either side of the resulting equation is a bare variable (whole side collapsed to `Y0`).
7. Write the first accepted abstraction to `lemmas/abstracted_stitch/abstracted_stitch_lemma_NNNN.p`.

The output directory is wiped and recreated on each run to prevent stale files from previous executions.

Usage:
```
python python/run_stitch.py <big_step_dir> <output_dir> [--max-arity 3] [--iterations 3]
```

### `rust/src/core.rs`

**`collect()`** — after the OCaml parser loop, calls `run_stitch_script(proof_file, &lemmas_dir)`. The returned `.p` file paths are appended to `all_lemma_files` before `prove_lemmas`, so stitch lemmas go through the identical Vampire + Twee pipeline.

**`run_stitch_script()`** — invokes the Python script (preferring `.venv/bin/python` when present), then scans `<lemmas_dir>/abstracted_stitch*/` for `.p` files and returns a sorted list. Returns an empty list on any error (fail-safe).

### `rust/src/utils.rs`

**`load_lemma()`** — maps `abstracted_stitch_lemma_NNNN` names to the `abstracted_stitch/` subdirectory:
```rust
} else if lemma_name.starts_with("abstracted_stitch_lemma_") {
    vec![("abstracted_stitch".to_string(), lemma_name.to_string())]
```

### `rust/src/minimize.rs`

**`proof_uses_lemma()`** — updated stitch regex to match the current naming convention:
```rust
let stitch_alt = format!(r"abstracted_stitch_lemma_{}", num);
```

---

## Data Flow

```
big-step lemma files
        │
        └─ python/run_stitch.py
              │  (per-lemma: immediate subterms → stitch_core → apply pattern)
              │
              └─ lemmas/abstracted_stitch/abstracted_stitch_lemma_NNNN.p

All .p files across all modes → prove_lemmas (Vampire + Twee) → summary.json
summary.json → shorten → minimize
```

---

## Comparison with the OCaml `abstracted` Mode

| Property | OCaml `abstracted` | Stitch `abstracted_stitch` |
|---|---|---|
| Pattern shape | Flat `op(Xi, Xj)` only | Arbitrary depth |
| Pattern source | Hand-coded scan | Discovered by Stitch compression |
| Corpus scope | Single lemma | Single lemma (per-lemma) |
| Patterns per lemma | 1 | First valid pattern found |
| Soundness check | Same string ≥ 2 times | Same concrete subterm ≥ 2 times |
| Rejects bare-variable sides | No | Yes |

---

## Performance on `Equation650_implies_Equation448.p`

81 lemmas total. Pipeline runtime: ~97 seconds (`--parallel`).

**Abstraction yield:**

| | Count |
|---|---|
| Big-step lemmas processed | 81 |
| Valid abstractions produced | **12** |
| Rejected (no repeated subterm ≥ 2×) | 60 |
| Rejected (whole side collapsed to variable) | 9 |

**Proof lengths (stitch vs baseline, selected lemmas):**

| Lemma | big-step | small-step | abstracted | abstracted_stitch |
|---|---|---|---|---|
| 6 | 4 | 4 | 58 | 80 |
| 8 | 3 | 2 | 80 | **35** |
| 14 | 4 | 2 | 65 | 79 |
| 32 | 23 | 2 | 80 | 80 |

Stitch lemmas are always provable but never win on per-lemma proof length — an expected result, since more general statements are harder to prove from scratch. The intended value is reusability: a single proved stitch lemma could serve as a shared axiom across multiple later proof obligations, shortening the final combined proof even if its individual proof is long. This angle is not yet evaluated.

---

## Example Abstraction

**Lemma 8 — concrete (big-step):**
```
op(X2, op(op(X3, op(op(X1,X0),X0)), X2))
  = op(op(X2, op(op(X3, op(op(X1,X0),X0)), X2)), op(X0, op(op(X1,X0),X0)))
```

**Lemma 8 — abstracted_stitch:**
```
op(X2, op(Y0, X2))
  = op(op(X2, op(Y0, X2)), op(X0, op(op(X1, X0), X0)))
```

The subterm `op(X3, op(op(X1,X0),X0))` appears twice in the original; replacing both with `Y0` yields a statement provable for *any* `Y0`. The original is an instance under `Y0 := op(X3, op(op(X1,X0),X0))`.

---

## Files Changed

| File | Type | Change |
|---|---|---|
| `python/run_stitch.py` | Modified | Rewritten for per-lemma approach; single `abstracted_stitch/` output dir |
| `python/demo_stitch.py` | New | Step-by-step illustration (toy example) |
| `python/demo_compare.py` | New | End-to-end demo with proof-length comparison table |
| `rust/src/core.rs` | Modified | `run_stitch_script()` with venv detection; updated dir scan |
| `rust/src/utils.rs` | Modified | `load_lemma()` handles `abstracted_stitch_lemma_NNNN` names |
| `rust/src/minimize.rs` | Modified | `proof_uses_lemma()` regex for `abstracted_stitch_` prefix |
| `CLAUDE.md` | New | Developer guide with pre-commit checklist and stitch notes |

---

## Next Steps

1. **Shared-axiom evaluation** — add proved stitch lemmas as additional axioms when running the prover on later lemmas, and measure whether any subsequent proof becomes shorter.
2. **Multiple patterns per lemma** — currently only the first valid pattern is applied; applying several simultaneously (with distinct variables `Y0, Y1, ...`) could yield stronger generalisations.
3. **Cross-lemma patterns** — Stitch was designed for corpus-wide compression. Running it across all big-step lemma bodies at once could find patterns recurring *across* lemmas, not just within one. (Blocked by a `stitch_core` assertion failure at large corpus sizes; needs investigation.)
