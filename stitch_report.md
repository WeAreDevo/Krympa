# Stitch integration status

Updated 2026-09-28. Problem: `Equation650_implies_Equation448.p`.

The measurements below precede the merge of parent repository commit `7c19dec`.
The corrected-version measurements describe `a340740`. Upstream adds
`--term-size`, new prover binaries, and trivial-inequality-removal step counting,
so these measurements are retained as historical baselines rather than claimed
as results of the merged version. The merged branch passes the Stitch and
term-size regression suites; a new comparative benchmark is still needed for
claims about its proof lengths or performance.

## Historical results verified at `0af5af4`

The audit reproduced 81 extracted lemmas, 12 generated Stitch abstractions,
and successful proofs for all 12. Collection chose 70 small-step and 11 big-step
winners, with zero wins for either abstraction mode.

| Lemma | big-step | small-step | abstracted | abstracted_stitch |
|---|---:|---:|---:|---:|
| 6 | 4 | 4 | 58 | 80 |
| 8 | 3 | 2 | 80 | 35 |
| 14 | 4 | 2 | 65 | 79 |
| 32 | 23 | 2 | 80 | 80 |

These are Krympa inference counts, not counts of every printed proof line.
All four published rows reproduced. The reported rejection breakdown of 60/9
was incorrect: instrumentation found 41 lemmas without an accepted candidate
before the bare-side filter and 28 rejected by that filter. An absent candidate
is not proof that the original equation has no repeated subterm.

The historical ~97-second total did not reproduce. The isolated audit run took
291.69 seconds (4.34 initial Vampire, 79.16 collect, 8.21 shorten, 199.98 minimize)
and produced a 27-step final proof versus 81 initial steps. It used macOS arm64,
`stitch-core==0.1.29`, a fresh debug build, and parallel execution with debug logs.
Timing depends on machine load, build settings, timeouts, and artifact state.

## Corrected implementation

The fixes address stale output reuse, Stitch winner lookup and DAG handling,
Vampire-only dependency loss, failed-output scoring, nested pattern matching,
fresh-variable selection, and comparison reporting. `AGENTS.md` replaces the
outdated Claude-specific guide. The historical audit remains in
`STITCH_AUDIT.md`; current behavior is documented in `STITCH_INTEGRATION.md`.

Nested matching and normalized whole-side exclusion change the generated
candidates. With the same 81 lemma inputs, the corrected generator produces
14 candidates: 6, 7, 8, 14, 23, 31, 32, 49, 54, 55, 56, 57, 61, and 62.
Instrumentation finds 63 lemmas without an accepted candidate before the
bare-side check and 4 rejected by that check. All 14 candidates receive successful
proofs in fresh collection. Winners remain 70 small-step and 11 big-step;
there are no Stitch winners.

| Lemma | Corrected Stitch proof length |
|---|---:|
| 6 | 35 |
| 7 | 69 |
| 8 | 35 |
| 14 | 79 |
| 23 | 61 |
| 31 | 80 |
| 32 | 80 |
| 49 | 82 |
| 54 | 67 |
| 55 | 98 |
| 56 | 82 |
| 57 | 78 |
| 61 | 80 |
| 62 | 50 |

These measurements use saved collection proofs with explicit successful status.
Candidate formulas can change when enumeration changes, so these scores should
not be substituted into the historical table as if the formulas were identical.

The corrected full run completed in 297.74 seconds: 3.50 initial Vampire,
75.63 collect, 8.20 shorten, and 210.41 minimize. It produced a 23-step final
proof versus 81 initial steps, with arrival `small_step_lemma_0078` and departure
`small_step_lemma_0026`. This uses the same environment as the historical audit.
It is not a Stitch speedup: no Stitch candidate won. Dependency recovery and
prover/search variability also affect the resulting minimized proof.

Validation: 44 Rust tests and 7 Python tests pass; all 14 generated candidates
pass the structural substitution invariant. Forced-winner tests exercise Stitch
lookup, dependency loading, DAG traversal, shortening, and Vampire-only support.

## Interpretation and next experiment

Universally replacing one concrete subterm consistently yields a statement at
least as strong as the original. A proof of the abstraction implies the original
by substitution. Two occurrences do not guarantee provability, and they are a
usefulness heuristic rather than a requirement for that implication.

The historical zero-win run shows no measured contribution from Stitch to the
final proof reduction. It does not establish that abstraction is inherently
unhelpful. The existing `shorten` phase already reuses winning abstracted
formulas in later problems, and minimization performs dependency analysis and
re-proving rather than simple concatenation.

Next, discover abstractions across lemmas and evaluate a reuse metric tied to
actual proof cost. Include the cost of proving shared abstractions and the cost
of the obligations that use them. Compare against the same baseline problem
and prover budgets. Compression size and occurrence count alone are not proof
shortening results. This research experiment is not implemented by the current
correctness patch.
