# HeytingLean ↔ Wolfram Bridge (Local FFI Scaffold)

This directory provides a **local-only** scaffold for connecting Wolfram Language (Wolfram Engine)
to **native artifacts produced by HeytingLean** (Lean→C export, compiled to a shared library).

It is designed to:
- exercise the C backend/linker (`.so`) path, and
- optionally run Wolfram Language FFI checks when `wolframscript` is installed.

## Quickstart

From the repo root:

```bash
./scripts/qa_wolfram_bridge.sh
```

Standalone tutorial (not part of the integrated workflow):

```bash
./scripts/qa_wolfram_tutorial.sh
```

For “Wolfram-required” verification (fails if Wolfram/WSTP aren’t usable):

```bash
./scripts/qa_wolfram_bridge.sh --strict
```

This will:
1) run `lake exe lambda_kernel_export` to emit C under `dist/lambda_kernel_export/`,
2) build a native test driver and compare stdout against `expected.txt`,
3) build `libheyting_kernel.so` and sanity-check it via `ctypes`,
4) (optional) run a Wolfram script using `ForeignFunctionLoad` if `wolframscript` exists.

## Hypergraph models (Wolfram Physics / SetReplace)

This repo also includes a hypergraph-evolution pipeline that can:

- run a small suite of Wolfram Physics-style models (Wolfram Engine + SetReplace), or
- fall back to a pure-Python rewriter if Wolfram isn't installed.

Commands:

```bash
./scripts/build_hypergraph_analysis.sh
./scripts/run_all_models.sh
```

Notebook-driven runs (extract `WolframModel` calls from a `.nb` and run headless):

```bash
./scripts/run_notebook_hypergraph.sh ~/Downloads/claude_test_hypergraph.nb 0   # list discovered calls
./scripts/run_notebook_hypergraph.sh ~/Downloads/claude_test_hypergraph.nb 1 10 /tmp/nb_run
```

Lossless Lean ↔ Wolfram roundtrip demo:

```bash
lake exe wolfram_roundtrip -- --echo
lake exe wolfram_roundtrip -- --notebook ~/Downloads/claude_test_hypergraph.nb --index 1 --steps 10
```

## Proof graphs (Lean proof term → hypergraph → Wolfram viz)

This repo can also export a Lean proof term (or type) into a **Wolfram-Physics-style hypergraph**
where each hyperedge is `premises ++ [conclusion]` (children → parent), then:

- render it in Wolfram (WolframModelPlot / HypergraphPlot), and
- generate a deterministic structural witness in Wolfram (a derivation/toposort) and verify it back in Lean.

Example:

```bash
cd lean
lake exe proof_term_hypergraph -- \
  --module HeytingLean.Crypto.QKD.BB84 \
  --const HeytingLean.Crypto.QKD.BB84.copyAll_impossible \
  --expr value --fuel 1024 --viz --witness
```

Outputs land under `.tmp/proof_term_hypergraph/<slug>/`, including:
- `*_hypergraph.bin` + `*_lengths.bin` (int64 LE, compatible with the existing C/Python readers)
- `*_metadata.json` + `*_graph.json`
- `*_term_hypergraph.png` + `*_term_dag.png`

Defaults:

- output base: `HYPERGRAPH_OUTPUT_BASE=/tmp/hypergraph_analysis_py`
- backend: `HYPERGRAPH_BACKEND=auto` (`wolfram` if `wolframscript` is activated + `SetReplace\`` loads, else `python`)
- quick mode: `HYPERGRAPH_QUICK=1` (10 steps per model)

## Files

- `test_kernel_ctypes.py`: loads `libheyting_kernel.so` and validates `heyting_add1` + `heyting_add2`.
- `test_wolfram_to_heyting_kernel.wls`: Wolfram Language FFI test (requires `wolframscript`).
- `wstp_client.c`: minimal WSTP client example (requires Wolfram WSTP SDK; optional).
- `notebook_hypergraph_analysis.wls`: extracts `WolframModel` examples from notebooks and runs them headlessly.
- `echo_hypergraph_binary.wls`: parse+re-emit hypergraph binaries (used by `wolfram_roundtrip -- --echo`).
- `proof_hypergraph_visualize.wls`: render a Lean-exported proof hypergraph to `.png` files.
- `proof_hypergraph_witness.wls`: produce a derivation/toposort witness from a proof hypergraph (JSON on stdout).

## Requirements

- Required: a C compiler (`cc`/`gcc`/`clang`), `python3`.
- Optional (Wolfram → C): `wolframscript` (Wolfram Engine).
- Optional (C → Wolfram): WSTP SDK headers/libs (varies by installation).

## Configuration knobs

- `HEYTING_WOLFRAM_LIB`: path to the `.so` passed to the Wolfram script.
- `WSTP_DIR`: directory containing `wstp.h` and the WSTP libraries (for building `wstp_client`).
- `WOLFRAM_KERNEL`: kernel launcher command for WSTP (default: `WolframKernel`).
