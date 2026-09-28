# Stitch abstraction integration

`collect` adds a fourth lemma mode, `abstracted_stitch`, alongside `big-step`,
`small-step`, and the OCaml `abstracted` heuristic. Production generation is
currently per lemma. Cross-lemma discovery and reuse scoring are planned next.

## Generation and logical contract

`python/run_stitch.py` parses each big-step conjecture, collects its immediate
compound subterms, excludes terms equal to either complete equation side after
normalizing whitespace, and deduplicates the corpus. It lambda-encodes the terms
and calls `stitch_core.compress(iterations=3, max_arity=3)`.

For each returned first-order pattern, it enumerates matching subterms at all
depths, including nested matches, groups by concrete term, and chooses the most
frequent group. At least two identical occurrences are required by this mode.
It replaces every occurrence of that one term with a fresh universally
quantified variable (`Y0`, or the next unused `Yn`). The first candidate leaving
both equation sides compound is written to:

```text
lemmas/abstracted_stitch/abstracted_stitch_lemma_NNNN.p
```

The original equation must be recoverable by substituting the concrete term for
that variable. Thus **a proved abstraction implies the original**. The abstracted
statement is at least as strong as the original, and must be proved separately.
Repeated occurrences and compound sides are selection heuristics; neither is a
logical requirement for sound instantiation or a guarantee of provability.

The OCaml baseline chooses the first repeated flat `op(...)` term, falling back
to the first flat term if none repeats. It does not maximize occurrence count
and does not require two occurrences.

## Rust integration

- `core::collect` clears the current Stitch output before invoking Python,
  prefers `.venv/bin/python`, and accepts files only after successful execution.
  Partial output from a failed invocation is discarded. Discovery is restricted
  to the current mode and its filename convention; legacy numbered/combined
  directories are ignored.
- The Python CLI also clears current output before checking for absent or empty
  input directories. Rust's pre-launch cleanup covers Python import failures.
- All generated problems enter the normal Vampire/Twee proving queue. Only
  explicit `Theorem` or `Unsatisfiable` result statuses are eligible as proofs.
- `load_lemma`, `select_actual_lemma`, dependency parsing, DAG traversal, and
  minimization support Stitch winners. Axiom recognition accepts numeric `aN`
  and `a_N` names, not every name starting with `a`.
- When a successful Twee proof is unavailable, dependency precomputation maps
  the named premises present in the Vampire refutation back to the lemma's
  TPTP input and selected dependency proofs. Unreadable or unresolved inputs
  cause an error rather than silently inventing an empty dependency list.
- `shorten` already substitutes winning abstracted formulas into later
  small-step problems and re-proves them. `minimize` analyzes DAGs and re-proves
  candidate combinations. Minimize errors propagate as a nonzero CLI exit.

These parsers target the equational TPTP emitted by this repository, not arbitrary
TPTP syntax. Dependency precomputation still prefers a successful Twee proof
when available, even when Vampire won the local score; joint optimization across
both proof DAGs remains outside the current implementation.

## Running and validation

```sh
# From the repository root:
.venv/bin/python python/run_stitch.py lemmas/big-step lemmas
PYTHONDONTWRITEBYTECODE=1 .venv/bin/python -m unittest discover -s python/tests -v

# Build/test from rust/:
cargo build --offline
cargo test --offline

# From the repository root, run all phases and compare successful proofs:
.venv/bin/python python/demo_compare.py
# Or inspect the currently saved results:
.venv/bin/python python/demo_compare.py --skip-pipeline
```

The comparison tool builds the current source binary in `rust/target/debug`
without replacing tracked executables. It displays all saved lemma rows,
recognizes the current Stitch mode, excludes failed/unknown/counter-satisfiable
outputs, and reports missing saved attempts relative to the collection summary.
`--skip-pipeline` assumes the shared proof directories still belong to the
selected problem. Run fresh comparisons in an isolated workspace when preserving
existing results matters.

Regression tests cover nested matches, substitution recovery, fresh variables,
stale/partial output, status filtering, a forced Stitch winner and its dependent
DAG, Vampire-only dependencies, and full comparison output. A benchmark with no
Stitch winners is insufficient to validate downstream Stitch handling.

## Results and next work

See `stitch_report.md` for measurements of the audited and corrected versions,
and `STITCH_AUDIT.md` for findings against historical commit `0af5af4`.

The parent repository's `--term-size` option is now integrated. During
minimization, it can prefer a proof with smaller average terms over one with
fewer steps, within the upstream 1.5x length tolerance. Collection still selects
by local step count. The option is separate from cross-lemma reuse scoring.
Upstream also counts Vampire's trivial inequality removal steps; the Python
comparison now mirrors that convention.

`demo_stitch.py` is a corpus-wide toy illustration; `inspect_proof_stitch.py`
explores patterns in an existing minimized proof. Their displayed abstractions
are proposals, not certified theorems.

The next experiment will discover patterns across lemmas and score candidate
abstractions using downstream reuse and total proof cost, including their own
proofs. Current selection still chooses the shortest local proof per lemma;
proved nonwinning Stitch lemmas are not globally offered as shared axioms.
