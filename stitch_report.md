# Stitch Abstraction Integration — Status Report

**Branch:** `feature/stitch_abstractions`  
**Test problem:** `Equation650_implies_Equation448.p`  
**Date:** 2026-05-12

---

## Background

Krympa proves equational theorems by extracting intermediate lemmas from a Vampire proof, re-proving each lemma with both Vampire and Twee in three modes (big-step, small-step, abstracted), then assembling the shortest proofs into a final output. This work adds a fourth mode — **abstracted_stitch** — that uses the [Stitch](https://github.com/mlb2251/stitch) program-synthesis library to generate structurally generalised variants of each lemma, which are then offered to the same proving pipeline alongside the baseline modes.

---

## What Was Implemented

### Pipeline integration (`rust/src/core.rs`)

The `collect` phase, after running the OCaml parser to produce big-step / small-step / abstracted lemma files, now calls a Python stitch script:

```
collect()
  ├── OCaml parser → lemmas/{big-step,small-step,abstracted}/
  └── run_stitch.py → lemmas/abstracted_stitch/          ← new
```

The Rust side discovers every `.p` file in `abstracted_stitch/` and appends them to the prover job list, so they go through the exact same Vampire + Twee pipeline as the baseline modes. No changes were needed to the proving or scoring logic — stitch lemmas participate as peers.

### Per-lemma abstraction (`python/run_stitch.py`)

For each big-step lemma file, the script:

1. **Parses** the TPTP conjecture body into a prefix-term tree.
2. **Builds a corpus** of the *immediate subterms* of each side of the equation — i.e., one level down from the root — excluding the full LHS and RHS themselves. This prevents Stitch from abstracting an entire side of the equation.
3. **Encodes** each corpus term as a lambda expression with De Bruijn indices and calls `stitch_core.compress()` to find compressive patterns.
4. **Applies** each discovered pattern back to the original formula body:
   - Collects every subterm (at any depth) that matches the pattern.
   - Groups matches by their concrete FOF string; finds the group with the highest count.
   - Only proceeds if ≥ 2 occurrences of the same concrete subterm match — guaranteeing that replacing them with a fresh variable `Y0` produces a *strictly weaker* statement (the original is recoverable by substituting `Y0 = that subterm`).
5. **Rejects** the abstraction if either side of the resulting equation is a bare variable (which would indicate that the whole LHS or RHS was abstracted away, producing an unprovable fixed-point statement like `Y0 = t(Y0, ...)`).
6. Writes the accepted abstracted TPTP file to `lemmas/abstracted_stitch/`.

### Downstream plumbing (`rust/src/utils.rs`, `rust/src/minimize.rs`)

- `load_lemma` was extended to resolve `abstracted_stitch_lemma_NNNN` names to the `abstracted_stitch/` subdirectory.
- `proof_uses_lemma` regex was updated to match the `abstracted_stitch_` prefix so the minimize phase can correctly identify stitch lemmas used in a proof chain.

---

## Results on `Equation650_implies_Equation448.p`

The problem has **81 lemmas**. The full pipeline (run_vampire → collect → shorten → minimize) ran in ~97 seconds.

### Stitch abstraction yield

| | Count |
|---|---|
| Big-step lemmas processed | 81 |
| Lemmas with valid abstraction | **12** |
| Rejected (no repeated subterm ≥ 2×) | 60 |
| Rejected (whole side collapsed to variable) | 9 |

### Proof length comparison (selected lemmas)

| Lemma | big-step | small-step | abstracted | abstracted_stitch |
|---|---|---|---|---|
| 6 | 4 | 4 | 58 | 80 |
| 8 | 3 | 2 | 80 | **35** |
| 14 | 4 | 2 | 65 | 79 |
| 32 | 23 | 2 | 80 | 80 |

*(Full 81-lemma table: run `python python/demo_compare.py --skip-pipeline`)*

### Winner breakdown

| Mode | Wins |
|---|---|
| small-step | majority |
| big-step | several |
| abstracted_stitch | 0 |

---

## Interpretation

The stitch lemmas are provable — provers find proofs for all 12 — but their proofs are longer than the concrete baseline lemmas. This is expected: a more general statement is harder to prove from scratch.

However, **the per-lemma proof length metric is the wrong measure for generalised lemmas**. The value proposition of abstracted_stitch lemmas is different from baseline modes:

- A concrete lemma is proved once and used once.
- A generalised lemma, if added as an axiom, could be reused across *multiple* proof steps, potentially shortening the final combined proof even if its own proof is long.

The current pipeline (shorten + minimize) does not yet exploit this: it picks the winner per lemma independently and builds the final proof by concatenation. The next natural step is to evaluate whether any stitch lemma — when added as a shared axiom — allows the prover to discharge multiple later obligations in fewer steps.

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

The pattern `op(X3, op(op(X1, X0), X0))` appears twice in the original formula; replacing both occurrences with `Y0` yields a statement that holds for *any* `Y0` (not just that specific compound term). The original is an instance under `Y0 = op(X3, op(op(X1,X0),X0))`.

---

## Next Steps

1. **Shared-axiom evaluation**: add stitch lemmas as additional axioms when running the prover on later lemmas, measuring whether any subsequent proof becomes shorter.
2. **Combined abstraction**: currently only the first valid pattern per lemma is used; applying multiple patterns simultaneously could yield stronger generalisations.
3. **Cross-lemma patterns**: Stitch was originally designed for corpus-wide abstraction — running it across all big-step lemmas at once (once the assertion-failure bug in `stitch_core` is understood or avoided) could find patterns that recur *across* lemmas, not just within one.
