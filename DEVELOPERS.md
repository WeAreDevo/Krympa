# Developers Guide

## Repo Layout

- `rust/` — main Krympa implementation and binaries
- `shell/` — helper scripts for running one problem or the full benchmark suite
- `python/` — input-generation and output-conversion helpers
- `benchmarks/` — Lean benchmark files and generated benchmark inputs
- `ocaml/` — lemma extractor / parser support

## Build

From `rust/`:

```bash
./build.sh
```

Produces `rust/krympa` and `rust/benchmarking_binary`.

## Execution Modes

The `krympa` binary accepts `--sequential` or `--parallel` before the subcommand.
Default when neither flag is given is `--parallel`.

```bash
./krympa --parallel collect <input-file>
./krympa --sequential collect <input-file>
```

Use `--sequential` when debugging to get deterministic, interleaved-free log output.

The shell scripts `run_one` and `run` always run in parallel mode — they do not accept or forward execution mode flags.

## Term-Size Proof Selection

`--term-size` extends proof selection: a proof with lower average term size is
preferred when its step count is within 1.5× of the shorter proof's step count.
Strictly fewer steps still always wins.

```bash
./krympa --term-size minimize <input-file>
./krympa --sequential --term-size minimize <input-file>
```

## Logging

Controlled by `KRYMPA_LOG`:

```bash
KRYMPA_LOG=debug ./krympa --sequential minimize <input-file>
```

- default / `info` — high-level progress only
- `debug` — full per-lemma trace

## Pipeline Steps

Run from `rust/` with a single input file:

```
run_vampire  →  collect  →  shorten  →  minimize
```

Optional analysis step: `group`.

### Manual run (parallel, default)

```bash
INPUT=../benchmarks/input11/Equation650_implies_Equation448.p

./krympa run_vampire "$INPUT"
./krympa collect "$INPUT"
./krympa shorten "$INPUT"
./krympa minimize "$INPUT"
```

### Manual run (sequential, with debug logging)

```bash
INPUT=../benchmarks/input11/Equation650_implies_Equation448.p

KRYMPA_LOG=debug ./krympa --sequential run_vampire "$INPUT"
KRYMPA_LOG=debug ./krympa --sequential collect "$INPUT"
KRYMPA_LOG=debug ./krympa --sequential shorten "$INPUT"
KRYMPA_LOG=debug ./krympa --sequential minimize "$INPUT"
```

## Run One Problem End-to-End

From `shell/`:

```bash
./run_one ../benchmarks/input11/Equation650_implies_Equation448.p
```

Always runs parallel. Generates inputs from the corresponding `.lean` file before running. For debug output, use the manual pipeline with `--sequential` and `KRYMPA_LOG=debug` instead.

## Run the Full Benchmark Suite

From `shell/`:

```bash
./run           # default 600s per problem
./run 200       # custom timeout
```

Always runs parallel. Generates inputs for all `Proofs*.lean` files before running each. The first argument is the per-problem timeout in seconds (default 600). Logs are written to `benchmarks/output_logs/`. For debug output on a single problem, use the manual pipeline with `--sequential` and `KRYMPA_LOG=debug` instead.

## Generate Benchmark Inputs

From `shell/`:

```bash
python3 ../python/generate_input.py ../benchmarks/Proofs11.lean
```

Produces `../benchmarks/input11/`.

## Pre-commit Check

From `rust/`:

```bash
cargo fmt
cargo build
cargo test
```

CI enforces formatting — always run `cargo fmt` before committing.

## Clean Build Artifacts

From the repo root:

```bash
git clean -nd rust/target ocaml/_build   # preview
git clean -fd rust/target ocaml/_build   # actually remove
```
