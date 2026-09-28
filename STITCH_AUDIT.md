# Stitch integration audit

Reviewed 2026-09-28 at commit `0af5af47ff9800b740b1a4ce68a8982080b39e89`.

The principal benchmark counts and selected proof lengths reproduce, but the
integration cannot yet be treated as correct end to end. In particular, this
benchmark has no Stitch winners, so it does not test downstream handling of a
winning Stitch lemma. Focused reproductions expose failures on that path.

This document records the original audit before corrections. Production source
and the two reports were unchanged at the time of that audit. The subsequent
correctness patch addresses the findings below; see `STITCH_INTEGRATION.md` for
current behavior and `stitch_report.md` for corrected-version measurements.

## Changes attributable to Claude

Git explicitly credits Claude Sonnet 4.6 on:

- `0af5af4`: per-lemma Stitch rewrite, updated Rust integration, the
  Vampire-only fallback in `precompute_lemmas`, comparison and inspection tools,
  reports, and replacement Krympa/benchmarking binaries.
- `3057d58`: `CLAUDE.md` developer guide.
- `200e67f`: upstream merge, including binaries and minimization changes.

The initial Stitch integration and toy demo already appear in the earlier
`7cbd894` / `cca455e` work-in-progress history. Those commits do not carry a
Claude coauthor trailer, so their authorship cannot be established from Git.

## Reproduced results

Environment: macOS arm64, repository Vampire/Twee and OCaml parser, Python
3.11 virtual environment with `stitch-core==0.1.29`, freshly built Rust debug
binary, `--parallel`. All four phases were launched in an isolated temporary
workspace, preserving the existing repository results.

| Measurement | Observed |
|---|---:|
| Big-step lemmas | 81 |
| Generated Stitch abstractions | 12 |
| Stitch conjectures proved (explicit theorem status) | 12 |
| Small-step winners in collection summary | 70 |
| Big-step winners in collection summary | 11 |
| OCaml abstracted / Stitch winners | 0 / 0 |

| Lemma | big-step | small-step | abstracted | abstracted_stitch |
|---|---:|---:|---:|---:|
| 6 | 4 | 4 | 58 | 80 |
| 8 | 3 | 2 | 80 | 35 |
| 14 | 4 | 2 | 65 | 79 |
| 32 | 23 | 2 | 80 | 80 |

These four rows match both reports exactly. Length means the existing Krympa
inference-count metric, not every printed proof line. Counts above were taken
from outputs with an explicit successful theorem status, independently of the
comparison script's classification.

The generated lemma IDs are 6, 8, 14, 32, 47, 49, 54, 55, 56, 57, 61, and 62.
For every generated lemma, a structural comparison verified that at least two
`Y0` occurrences stand for the same concrete term and that substituting it back
recovers the original equation. The displayed lemma 8 example also matches.

## Findings

### High: Stitch winners cannot be resolved consistently downstream

`rust/src/utils.rs:177` (`select_actual_lemma`) only searches `small_step`,
`big_step`, and `abstracted` for a generic `lemma_NNNN` reference. It never
searches `abstracted_stitch`. Furthermore, its `starts_with('a')` axiom shortcut
misclassifies explicit `abstracted_stitch_lemma_NNNN` names as built-in axioms.
`rust/src/dag.rs:67` has the same prefix shortcut.

A fixture containing only `abstracted_stitch_lemma_0008_vampire.proof` produces:

```text
select_actual_lemma(..., "lemma_0008") -> None
select_actual_lemma(..., "abstracted_stitch_lemma_0008")
  -> Some("abstracted_stitch_lemma_0008")  # missing prover suffix
load_all_dependency_proofs(...) -> Cannot read proof file abstracted_stitch_lemma_0008
build_dag("abstracted_stitch_lemma_0008", ...) -> empty DAG
```

The broad axiom shortcut predates the new integration and also affects the
original abstracted mode. Extending `load_lemma` and `proof_uses_lemma` alone
does not complete Stitch support. Narrow axiom recognition, extend variant
resolution, and test a deliberately selected Stitch winner with dependents.

### High: failed Stitch runs can inject stale problems into collection

At `rust/src/core.rs:328`, an unsuccessful Python exit emits a warning but
continues to scan all directories beginning with `abstracted_stitch`.
The Python script only clears the current `abstracted_stitch/` directory after
imports and input checks; legacy numbered/combined directories remain eligible
even after a successful run.

An isolated fixture with a Python executable that exits 1 and one pre-existing
Stitch file logs both the error and `Stitch generated 1 lemma file(s)`, then
passes that stale file to the prover. Thus the integration guide's claim that
the helper returns an empty list on any error is false. Stale files can contain
another problem's axioms while competing under the current problem's lemma ID.

Return immediately on unsuccessful process status and restrict discovery to
fresh outputs of this invocation. Cleanup must also cover early exit paths and
the transition from legacy directory names.

### Medium: comparison tool can report false conjectures as zero-step proofs

`python/demo_compare.py:189` counts every saved prover output without checking
its result status. In the fresh benchmark, `abstracted_lemma_0081_twee.proof`
contains `RESULT: CounterSatisfiable`; the comparison code scores it as zero.
Consequently, its proof-length and "provable" statistics are not reliable in
general, even though the four published rows independently check out.

The same tool's `STITCH_RE` at line 33 requires a trailing underscore. Filename
parsing yields the mode `abstracted_stitch`, so the current mode is classified
as a baseline. A future Stitch winner would be counted as a baseline win.
The script also limits output to 40 rows, contrary to the report's instruction
that it prints the full 81-lemma table. On the pre-existing local results it
finds only 16 lemma IDs, demonstrating that `--skip-pipeline` depends on the
current contents of the shared proof directories.

### Medium: rejection breakdown does not reproduce

Instrumenting `apply_pattern_to_formula` without changing its behavior gives:

| Mutually exclusive per-lemma outcome | Observed | Reported |
|---|---:|---:|
| Accepted abstraction | 12 | 12 |
| No accepted candidate before the bare-side filter | 41 | 60 |
| At least one candidate produced, but all rejected for bare sides | 28 | 9 |

The 41 count must not be relabeled "no repeated subterm": the implementation
also returns `None` for absent patterns, compression/conversion failures, and
degenerate results. Its CLI emits only generated/skipped totals, so the reports'
more specific 60/9 split is not supported by the current implementation.

### Medium: reports reverse the logical strength and overstate soundness rules

The correct implication is **proved abstraction implies original**, by
substitution. Universally generalizing a concrete subterm gives a statement at
least as strong as the original, not a weaker statement. Strict strengthening
is not guaranteed, either.

Two occurrences are a candidate-selection heuristic, not a requirement for
this implication: it also holds for one occurrence of a fresh variable.
Conversely, two occurrences do not guarantee that the abstraction is provable.
All 12 are proved in this benchmark; "always provable" is not a general result.
Bare-variable sides also are not inherently unprovable (idempotence
`op(Y0,Y0) = Y0` is an obvious example in a suitable theory).

Using the same concrete term consistently is essential for recovery by this
single substitution. Replacing distinct terms by the same variable can instead
lose the implication to the original; the issue is not simply making the
abstracted statement false.

### Medium: matcher does not enumerate all matching subterms as documented

`python/run_stitch.py:392` returns immediately after an outer match, so nested
matches are not counted. For pattern `op(A,B)` and equation

```text
op(op(X0,X1),X2) = op(X3,op(X0,X1))
```

the implementation counts two different outer terms once each and returns
`None`. It misses the repeated inner `op(X0,X1)`, whose replacement would leave
both equation sides compound. Either enumerate nested matches before selecting
the concrete target, or describe and evaluate the actual outermost heuristic.

### Limit: the Vampire-only change avoids an error by discarding dependencies

`rust/src/utils.rs:65` registers a lemma with empty dependencies whenever reading
its Twee proof fails. This does not extract the dependencies of the available
Vampire proof, and it also swallows errors other than a missing file. It can
make the DAG incomplete; it is not a complete implementation of mixed-prover
dependency analysis. The fresh run has Vampire-only winners 28 and 47.

This observation alone does not establish that the emitted final proof is
invalid: minimization also re-proves obligations. It does mean that "minimize
bug fix" should be described as a fallback with a dependency-analysis limit.

## Other report corrections

- The OCaml heuristic at `ocaml/lib/lemma_extractor.ml:159` selects the first
  repeated flat term, not the most frequent term. If none repeats, it selects
  the first available flat term anyway. The integration guide's baseline
  description and its "same string >= 2 times" comparison entry are incorrect.
- `shorten_proofs` already substitutes winning abstracted formulas into later
  small-step problems and re-proves them (`rust/src/core.rs:101`). Minimization
  builds dependency DAGs and re-proves combinations. Describing the pipeline
  as only independent winner selection followed by concatenation is inaccurate.
  What is missing is an evaluation of sharing *nonwinning* Stitch lemmas more
  widely; no speedup from that proposed experiment has been demonstrated.
- `CLAUDE.md` and the module header of `run_stitch.py` still describe numbered
  and combined output directories. The toy demo uses a corpus-wide workflow,
  unlike production per-lemma generation. The inspection script runs, with
  compression retries on the existing proof, but its proposed abstractions
  are not proved by that script.

## Validation

- `cargo build --offline`: passed.
- `cargo test --offline`: all 39 tests passed; none specifically exercise Stitch.
- Fresh isolated collection: 81 summary entries; all 12 Stitch outputs have
  Vampire theorem status; published selected scores reproduced.
- Structural substitution check: passed for all 12 generated abstractions.
- Focused stale-file, winner-lookup, DAG, nested-match, and comparison-status
  reproductions: failures described above confirmed.
- Toy demo and existing-proof inspection script execute; the inspection script
  requires fallback compression settings for this corpus.

The fresh pipeline completed successfully:

| Phase | Seconds |
|---|---:|
| run_vampire | 4.34 |
| collect | 79.16 |
| shorten | 8.21 |
| minimize | 199.98 |
| Total | 291.69 |

Minimization reported 27 steps versus 81 initial steps, with arrival lemma
`small_step_lemma_0078` and departure lemma `small_step_lemma_0012`, and wrote a
new final proof. The historical ~97-second total was not reproduced. This is a
fresh debug build with debug logging; build settings, machine load, timeouts,
and prior artifact contents limit direct timing comparisons. In particular,
the existing repository proof directories were not a complete fresh run.

Zero Stitch winners means this run does not demonstrate a Stitch contribution
to the final reduction. This audit does not independently certify every
inference in the final assembled proof.

Raw logs, fresh lemma/proof outputs, instrumentation results, and the compiled
Rust regression fixture are retained for this session at:

```text
/private/var/folders/40/km8v2fd51731fpxmpgvn1nlr0000gn/T/krympa-stitch-audit-olx_2104/
```

The original audit added only this Markdown file. Pre-existing modified
build/cache files and untracked `rust/target/` were not cleaned or reverted.
The subsequent correctness patch adds targeted Rust and Python regressions;
this historical record retains the original findings and test counts.
