# Krympa — Claude Code Guide

## Repo Layout

- `rust/` — main Krympa implementation and binaries
- `shell/` — helper scripts (`run_one`, `run`)
- `python/` — input generation, Stitch abstraction pipeline
- `benchmarks/` — Lean benchmark files and generated inputs
- `ocaml/` — lemma extractor / TPTP parser

## Build

```bash
cd rust && ./build.sh
```

Produces `rust/krympa` and `rust/benchmarking_binary`. The committed binaries are macOS arm64 — do not overwrite with Linux builds.

## Running

### One problem end-to-end (preferred)

```bash
cd shell
./run_one ../benchmarks/input11/Equation650_implies_Equation448.p
./run_one --sequential ../benchmarks/input11/Equation650_implies_Equation448.p
KRYMPA_LOG=debug ./run_one ../benchmarks/input11/Equation650_implies_Equation448.p
```

### Full benchmark suite

```bash
cd shell && ./run 2700
KRYMPA_EXECUTION_MODE=--sequential KRYMPA_LOG=debug ./run 2700
```

### Manual pipeline steps (from `rust/`)

```bash
./krympa --parallel run_vampire "$INPUT"
./krympa --parallel collect "$INPUT"
./krympa --parallel shorten "$INPUT"
./krympa --parallel minimize "$INPUT"
```

Default execution mode is `--parallel`. Pass `--sequential` or `--execution-mode=sequential` to change it.

Logging: `KRYMPA_LOG=info` (default) or `KRYMPA_LOG=debug`.

## Before Every Commit

### 1. Clean build artifacts

Preview:
```bash
git clean -nd rust/target ocaml/_build
```

Remove:
```bash
git clean -fd rust/target ocaml/_build
```

### 2. Check compilation and tests

```bash
cd rust
cargo build --offline
cargo test --offline
```

Drop `--offline` if dependencies are not cached locally.

### 3. Confirm clean state

```bash
git status
```

## Stitch Integration (feature/stitch_abstractions)

`collect` runs a Python Stitch pipeline after the OCaml parser loop, producing `abstracted_stitch_N/` and `abstracted_stitch_combined/` lemma directories alongside `big-step/`, `small-step/`, `abstracted/`.

Key files:
- `python/run_stitch.py` — full pipeline
- `python/demo_stitch.py` — toy example (run with `.venv/bin/python python/demo_stitch.py`)
- `rust/src/core.rs` — calls `run_stitch_script()` inside `collect()`
- `rust/src/utils.rs` — `load_lemma()` handles `abstracted_stitch_(?:\d+|combined)` names
- `rust/src/minimize.rs` — `proof_uses_lemma()` regex covers stitch variants

Requires `stitch_core` Python package installed in `.venv` at repo root.
