#!/usr/bin/env python3
"""
demo_compare.py

Runs the full Krympa pipeline (Stitch-enabled) on one problem, then
prints a side-by-side comparison of proof lengths for baseline modes
(big-step, small-step, abstracted) vs. the Stitch-abstracted variants.

Usage (from anywhere in the repo):
    python python/demo_compare.py
    python python/demo_compare.py path/to/Problem.p
"""

import json
import re
import subprocess
import sys
import time

from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
RUST_DIR = REPO_ROOT / "rust"
KRYMPA = RUST_DIR / "krympa"
OUTPUT_DIR = REPO_ROOT / "output"
PROOFS_DIR = REPO_ROOT / "proofs"
LEMMAS_DIR = REPO_ROOT / "lemmas"
DEFAULT_INPUT = REPO_ROOT / "benchmarks/input11/Equation650_implies_Equation448.p"

SEP  = "=" * 72
SEP2 = "-" * 72

STITCH_RE = re.compile(r"^abstracted_stitch_")
PROOF_FILE_RE = re.compile(r"^(.+)_lemma_(\d{4})_(vampire|twee)\.proof$")

BASELINE_DISPLAY = {
    "big_step": "big-step",
    "small_step": "small-step",
    "abstracted": "abstracted",
}


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def section(title):
    print(f"\n{SEP}\n  {title}\n{SEP}")


def problem_suffix(path: Path) -> str:
    stem = path.stem
    return stem[len("input_problem_"):] if stem.startswith("input_problem_") else stem


def parse_proof_filename(name: str):
    """Return (mode_prefix, lemma_num, prover) or (None, None, None)."""
    m = PROOF_FILE_RE.match(name)
    if not m:
        return None, None, None
    return m.group(1), int(m.group(2)), m.group(3)


# Mirrors prover_wrapper.rs proof_length_vampire / proof_length_twee

def count_vampire_steps(text: str) -> int:
    keywords = ("demodulation", "superposition", "resolution")
    count = 0
    for line in text.splitlines():
        l = line.lstrip()
        if not l or l.startswith("%"):
            continue
        if "." in l:
            l = l[l.index(".") + 1:].lstrip()
        if "[" in l and any(kw in l for kw in keywords):
            count += 1
    return count


def count_twee_steps(text: str) -> int:
    in_proof = False
    count = 0
    for line in text.splitlines():
        l = line.lstrip()
        if l.startswith("Proof:"):
            in_proof = True
        elif in_proof and "= { by" in l:
            count += 1
    return count


def count_steps(prover: str, text: str) -> int:
    if "vampire" in prover:
        return count_vampire_steps(text)
    if "twee" in prover:
        return count_twee_steps(text)
    return text.count("\n")


def ensure_binary() -> bool:
    """Build krympa locally if the committed binary can't run on this platform."""
    test = subprocess.run([str(KRYMPA), "--help"], cwd=str(RUST_DIR),
                          capture_output=True)
    if test.returncode == 0 or b"Usage" in test.stdout:
        return True
    print(f"  Binary not runnable (format mismatch?). Building locally …")
    r = subprocess.run(["bash", "build.sh"], cwd=str(RUST_DIR))
    if r.returncode != 0:
        print("  [ERROR] Build failed. Run `cd rust && ./build.sh` manually.")
        return False
    print("  Build complete.\n")
    return True


def run_step(step: str, input_file: Path) -> bool:
    print(f"    [{step:<12}] ", end="", flush=True)
    t0 = time.time()
    r = subprocess.run(
        [str(KRYMPA), "--parallel", step, str(input_file)],
        cwd=str(RUST_DIR),
        capture_output=True,
        text=True,
    )
    elapsed = time.time() - t0
    if r.returncode == 0:
        print(f"done  ({elapsed:.1f}s)")
    else:
        print(f"FAILED ({elapsed:.1f}s)")
        if r.stderr:
            print("      " + r.stderr[-400:].replace("\n", "\n      "))
    return r.returncode == 0


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    skip = "--skip-pipeline" in sys.argv
    args = [a for a in sys.argv[1:] if a != "--skip-pipeline"]
    input_file = Path(args[0]).resolve() if args else DEFAULT_INPUT
    if not input_file.exists():
        print(f"[ERROR] Not found: {input_file}", file=sys.stderr)
        sys.exit(1)

    suffix = problem_suffix(input_file)

    # ------------------------------------------------------------------
    section("STEP 1 — Run Krympa pipeline (Stitch-enabled)")
    print(f"  Problem : {input_file.name}")
    print(f"  Binary  : {KRYMPA}\n")

    if skip:
        print("  (--skip-pipeline: reusing existing results)\n")
    else:
        if not ensure_binary():
            sys.exit(1)

    for step in ("run_vampire", "collect", "shorten", "minimize"):
        if skip:
            print(f"    [{step:<12}] skipped")
            continue
        if not run_step(step, input_file):
            print("\n  [ABORT] Pipeline step failed.")
            sys.exit(1)

    # ------------------------------------------------------------------
    section("STEP 2 — Stitch abstraction directories produced")

    stitch_dirs = sorted(LEMMAS_DIR.glob("abstracted_stitch*/"))
    if not stitch_dirs:
        print("  None — stitch_core may not be installed in .venv, or no patterns found.")
        print("  Tip: pip install stitch-core  (inside .venv)")
    else:
        for d in stitch_dirs:
            files = sorted(d.glob("*.p"))
            print(f"  {d.name}/   ({len(files)} lemma files)")

    # ------------------------------------------------------------------
    section("STEP 3 — Per-lemma proof length comparison")

    # Collect all intermediate proof files (every attempted mode is kept here)
    # key: (lemma_num, mode_prefix) -> best_steps across provers
    best: dict[tuple, int] = {}

    for tmp_dir in (PROOFS_DIR / "vampire_tmp", PROOFS_DIR / "twee_tmp"):
        if not tmp_dir.exists():
            continue
        for f in sorted(tmp_dir.glob("*.proof")):
            mode, num, prover = parse_proof_filename(f.name)
            if num is None:
                continue
            text = f.read_text(errors="replace")
            steps = count_steps(prover, text)
            key = (num, mode)
            if key not in best or steps < best[key]:
                best[key] = steps

    # Determine which mode prefixes exist
    all_lemma_nums = sorted({num for num, _ in best})
    baseline_modes = sorted({mode for _, mode in best if not STITCH_RE.match(mode or "")})
    stitch_modes = sorted({mode for _, mode in best if STITCH_RE.match(mode or "")})

    if not all_lemma_nums:
        print("  No proof files found in proofs/vampire_tmp or proofs/twee_tmp.")
        sys.exit(0)

    # Load summary to find the winner per lemma
    summary_winner: dict[int, str] = {}
    summary_path = OUTPUT_DIR / f"summary_{suffix}.json"
    if summary_path.exists():
        for k, v in json.loads(summary_path.read_text()).items():
            mode_stem = v[0]  # e.g. "abstracted_stitch_0_lemma_0003"
            m = re.match(r"^(.+)_lemma_\d{4}$", mode_stem)
            if m:
                summary_winner[int(k)] = m.group(1)

    # Column layout
    col = 7
    stitch_short = {m: m.replace("abstracted_stitch_", "stitch_") for m in stitch_modes}
    display_modes = baseline_modes + stitch_modes
    headers = [BASELINE_DISPLAY.get(m, m) for m in baseline_modes] + \
              [stitch_short[m] for m in stitch_modes]

    lw = 7
    header_line = f"  {'lemma':>{lw}}" + "".join(f"  {h:>{col}}" for h in headers) + "   winner"
    print(header_line)
    print(f"  {'─'*lw}" + "".join(f"  {'─'*col}" for _ in display_modes) + "   ──────")

    # Stats counters
    stitch_wins = 0
    stitch_strictly_better = 0
    stitch_only = 0
    total = len(all_lemma_nums)

    display_limit = 40
    for i, num in enumerate(all_lemma_nums):
        row_vals = {mode: best.get((num, mode)) for mode in display_modes}
        winner = summary_winner.get(num, "")
        winner_label = stitch_short.get(winner, BASELINE_DISPLAY.get(winner, winner))

        if i < display_limit:
            cells = "".join(
                f"  {str(v):>{col}}" if v is not None else f"  {'—':>{col}}"
                for v in row_vals.values()
            )
            print(f"  {num:>{lw}d}{cells}   {winner_label}")

        # Stats
        is_stitch_win = bool(STITCH_RE.match(winner))
        if is_stitch_win:
            stitch_wins += 1
            baseline_best = min((v for m, v in row_vals.items()
                                 if not STITCH_RE.match(m) and v is not None), default=None)
            stitch_best = min((v for m, v in row_vals.items()
                               if STITCH_RE.match(m) and v is not None), default=None)
            if baseline_best is None:
                stitch_only += 1
            elif stitch_best is not None and stitch_best < baseline_best:
                stitch_strictly_better += 1

    if total > display_limit:
        print(f"  ... ({total - display_limit} more lemmas omitted)")

    # ------------------------------------------------------------------
    section("STEP 4 — Aggregate statistics")

    print(f"  Lemmas in summary                 : {total}")
    print(f"  Stitch mode was the winner        : {stitch_wins}  ({100*stitch_wins//max(total,1)}%)")
    if stitch_wins:
        print(f"    strictly shorter than baseline  : {stitch_strictly_better}")
        print(f"    baseline could not prove at all : {stitch_only}")
    print(f"  Baseline won                      : {total - stitch_wins}  ({100*(total-stitch_wins)//max(total,1)}%)")

    if stitch_modes:
        print(f"\n  Stitch patterns found             : {len(stitch_modes)}")
        for m in stitch_modes:
            proved = sum(1 for num in all_lemma_nums if best.get((num, m)) is not None)
            print(f"    {stitch_short[m]:<28}: {proved} / {total} lemmas provable")

    # ------------------------------------------------------------------
    section("STEP 5 — Minimize output")
    

    proof_out = OUTPUT_DIR / f"proof_{suffix}.out"
    if proof_out.exists():
        lines = [l for l in proof_out.read_text().splitlines() if l.strip()]
        print(f"  File   : {proof_out.name}")
        print(f"  Length : {len(lines)} lines\n")
        preview = lines[:25]
        for l in preview:
            print(f"    {l}")
        if len(lines) > 25:
            print(f"    ... ({len(lines) - 25} more lines)")
    else:
        print(f"  No proof_{suffix}.out produced.")
        print(f"  (Minimize may have found no valid candidate, or hit a known limitation:")
        print(f"   precompute_lemmas requires a twee proof for every winner, but vampire-only"
              f" lemmas have no twee_tmp entry.)")

    print()


if __name__ == "__main__":
    main()
