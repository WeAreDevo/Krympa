# Krympa development guide

## Layout and build

- `rust/`: orchestration, proof scoring, dependency analysis, minimization.
- `ocaml/`: Vampire lemma extraction and TPTP generation.
- `python/`: Stitch abstraction, inspection, and comparison tools.
- `bin/`: platform-specific Vampire and Twee executables.
- `shell/`: single-problem and benchmark runners.

Build and test from `rust/`:

```sh
cargo build --offline
cargo test --offline
```

The build requires Dune and OCaml. Python abstraction requires the repository
virtual environment with `stitch-core` installed (audit version: 0.1.29).
Run Python regression tests from the repository root:

```sh
PYTHONDONTWRITEBYTECODE=1 .venv/bin/python -m unittest discover -s python/tests -v
```

Use `rust/target/debug/krympa` for source validation. `rust/build.sh` also copies
binaries into tracked paths; do not update those binaries incidentally or
replace a platform's binaries with another platform's build.

## Running

Work from `rust/` for direct CLI calls:

```sh
target/debug/krympa --parallel run_vampire "$INPUT"
target/debug/krympa --parallel collect "$INPUT"
target/debug/krympa --parallel shorten "$INPUT"
target/debug/krympa --parallel minimize "$INPUT"
```

Parallel execution is the default; `--sequential` is available.
`KRYMPA_LOG=debug` enables detailed logs; normal logging defaults to `info`.
The phases share and overwrite `lemmas/`, `proofs/`, `tmp/`, and `output/` under
the parent of the working directory. Preserve existing results and use an
isolated workspace for benchmarks. Do not run different problems concurrently
against those shared directories.

## Stitch invariants

The current production mode is per lemma. `python/run_stitch.py` writes only
`lemmas/abstracted_stitch/abstracted_stitch_lemma_NNNN.p`. Numbered/combined
directories are legacy outputs and must not participate in collection.

- Replace occurrences of one identical concrete term with one fresh variable.
  Instantiating that variable must recover the original equation.
- The universally quantified abstraction is at least as strong as the original;
  repeated occurrences do not guarantee provability. Prove every candidate.
- Only explicit theorem/unsatisfiable statuses count as proofs. A countermodel,
  timeout, unknown result, or missing status must never become a zero-step win.
- A winning Stitch lemma must survive generic dependency lookup, DAG traversal,
  shortening, and minimization. Test a forced Stitch winner; a zero-win benchmark
  does not exercise this path.
- Missing Twee output must not erase the dependencies of a Vampire proof.
- Failed generation must not leave stale candidates eligible for collection.

`STITCH_AUDIT.md` records the historical audit at `0af5af4`.
`STITCH_INTEGRATION.md` describes current behavior; `stitch_report.md` separates
historical measurements from measurements of the corrected implementation.
The toy and inspection scripts explore corpus-wide patterns; their candidate
formulas are not automatically proved.

## Changes and commits

Add focused regression coverage for proof correctness, scoring, and dependency
changes. Run the Rust and Python suites and `git diff --check` before committing.
Do not stage generated proofs, caches, build directories, or incidental binaries.
Do not clean or revert pre-existing user changes. Preserve them when merging.
Use ordinary merge commits for upstream integration unless instructed otherwise.

## Next research direction

The planned next phase is cross-lemma abstraction discovery, with scoring based
on actual reuse and the total cost of the combined proof, including the cost of
proving shared abstractions. This is separate from the current correctness fix.
Compression size alone is not evidence of proof shortening. Retain baseline
comparisons, prove candidate abstractions, and measure their use in downstream
obligations before claiming an improvement.
