# Developing Krympa

This guide is for new developers who want to build Krympa, run the pipeline,
switch between parallel and sequential execution, enable debug logging, and
clean local build artifacts before committing.

## Repo Layout

- `rust/`: main Krympa implementation and binaries
- `shell/`: helper scripts for running one problem or the full benchmark suite
- `python/`: input-generation and output-conversion helpers
- `benchmarks/`: Lean benchmark files and generated benchmark inputs
- `ocaml/`: lemma extractor / parser support

## Build

Build the Rust binaries from the `rust/` directory:

```bash
cd rust
./build.sh
```

This produces:

- `rust/krympa`
- `rust/benchmarking_binary`

## Execution Modes

Krympa now supports two execution modes:

- `--parallel`
- `--sequential`

If you do not pass either flag, the default is `--parallel`.

Both of these forms work:

```bash
./krympa --sequential collect <input-file>
./krympa --execution-mode=sequential collect <input-file>
```

## Logging

Logging is controlled with the `KRYMPA_LOG` environment variable.

- normal logs: default, or `KRYMPA_LOG=info`
- debug logs: `KRYMPA_LOG=debug`

Examples:

```bash
./krympa --parallel collect <input-file>
KRYMPA_LOG=debug ./krympa --parallel collect <input-file>
./krympa --sequential collect <input-file>
KRYMPA_LOG=debug ./krympa --sequential collect <input-file>
```

## Pipeline Overview

The main pipeline steps are:

1. `run_vampire`
2. `collect`
3. `shorten`
4. `minimize`

Optional analysis step:

5. `group`

When running the raw binary directly, work from `rust/`.

## Run One Step Manually

Example input:

```bash
cd rust
INPUT=../benchmarks/input11/Equation650_implies_Equation448.p
```

### `run_vampire`

```bash
./krympa --parallel run_vampire "$INPUT"
KRYMPA_LOG=debug ./krympa --parallel run_vampire "$INPUT"
./krympa --sequential run_vampire "$INPUT"
KRYMPA_LOG=debug ./krympa --sequential run_vampire "$INPUT"
```

### `collect`

```bash
./krympa --parallel collect "$INPUT"
KRYMPA_LOG=debug ./krympa --parallel collect "$INPUT"
./krympa --sequential collect "$INPUT"
KRYMPA_LOG=debug ./krympa --sequential collect "$INPUT"
```

### `shorten`

```bash
./krympa --parallel shorten "$INPUT"
KRYMPA_LOG=debug ./krympa --parallel shorten "$INPUT"
./krympa --sequential shorten "$INPUT"
KRYMPA_LOG=debug ./krympa --sequential shorten "$INPUT"
```

### `group`

```bash
./krympa --parallel group "$INPUT"
KRYMPA_LOG=debug ./krympa --parallel group "$INPUT"
./krympa --sequential group "$INPUT"
KRYMPA_LOG=debug ./krympa --sequential group "$INPUT"
```

### `minimize`

```bash
./krympa --parallel minimize "$INPUT"
KRYMPA_LOG=debug ./krympa --parallel minimize "$INPUT"
./krympa --sequential minimize "$INPUT"
KRYMPA_LOG=debug ./krympa --sequential minimize "$INPUT"
```

## Run The Full Manual Pipeline

From `rust/`:

```bash
./krympa --parallel run_vampire "$INPUT"
./krympa --parallel collect "$INPUT"
./krympa --parallel shorten "$INPUT"
./krympa --parallel minimize "$INPUT"
```

Sequential version:

```bash
./krympa --sequential run_vampire "$INPUT"
./krympa --sequential collect "$INPUT"
./krympa --sequential shorten "$INPUT"
./krympa --sequential minimize "$INPUT"
```

Debug + sequential version:

```bash
KRYMPA_LOG=debug ./krympa --sequential run_vampire "$INPUT"
KRYMPA_LOG=debug ./krympa --sequential collect "$INPUT"
KRYMPA_LOG=debug ./krympa --sequential shorten "$INPUT"
KRYMPA_LOG=debug ./krympa --sequential minimize "$INPUT"
```

## Generate Benchmark Inputs

From `shell/`:

```bash
cd shell
python3 ../python/generate_input.py ../benchmarks/Proofs11.lean
```

This generates a folder like:

```bash
../benchmarks/input11/
```

## Run One Problem End-To-End

From `shell/`:

```bash
./run_one ../benchmarks/input11/Equation650_implies_Equation448.p
```

Debug:

```bash
KRYMPA_LOG=debug ./run_one ../benchmarks/input11/Equation650_implies_Equation448.p
```

Sequential:

```bash
./run_one --sequential ../benchmarks/input11/Equation650_implies_Equation448.p
```

Debug + sequential:

```bash
KRYMPA_LOG=debug ./run_one --sequential ../benchmarks/input11/Equation650_implies_Equation448.p
```

Using a specific Krympa binary:

```bash
./run_one --sequential ../benchmarks/input11/Equation650_implies_Equation448.p ./krympa_bs
```

## Run The Full Benchmark Suite

From `shell/`:

```bash
./run 2700
```

Debug:

```bash
KRYMPA_LOG=debug ./run 2700
```

Sequential:

```bash
KRYMPA_EXECUTION_MODE=--sequential ./run 2700
```

Debug + sequential:

```bash
KRYMPA_EXECUTION_MODE=--sequential KRYMPA_LOG=debug ./run 2700
```

Using a specific binary:

```bash
KRYMPA_EXECUTION_MODE=--sequential KRYMPA_LOG=debug ./run 2700 ./krympa_bs
```

Logs are written to:

```bash
../benchmarks/output_logs/
```

## Clean Rust And OCaml Artifacts Before Committing

From the repo root:

Preview what would be removed:

```bash
git clean -nd rust/target ocaml/_build
```

Actually remove those generated directories:

```bash
git clean -fd rust/target ocaml/_build
```

Then confirm the repo is clean enough to commit:

```bash
git status
```

## Recommended Pre-Commit Check

From `rust/`:

```bash
cargo build --offline
cargo test --offline
```

If dependencies are not already cached locally, drop `--offline`.
