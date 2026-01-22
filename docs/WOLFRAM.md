---
title: Wolfram Physics Connection
description: Lean ↔ Wolfram bridge, demos, and cross-checks
---

# Wolfram Physics Connection

This repo includes a minimal Lean ↔ Wolfram bridge to demonstrate that the multiway / branchial constructions used in Wolfram Physics align with the formal multiway semantics implemented in Lean.

## What’s Included

- Lean CLIs:
  - `wolfram_multiway_demo` — small finite multiway evolution with branchial edges.
  - `wolfram_wm148_demo` — WM148 rule (`{{x,y}} -> {{x,y},{y,z}}`) with Nat vertices.
  - `wolfram_roundtrip` — binary echo using Wolfram Language (lossless Lean→WL→Lean).
- WL scripts in `RESEARCHER_BUNDLE/ffi/heyting_wolfram_bridge/`:
  - `echo_hypergraph_binary.wls` — parse and re-emit Lean’s compressed hypergraph.
  - `proof_hypergraph_visualize.wls` — render Lean-exported proof hypergraphs.
  - `notebook_hypergraph_analysis.wls` — extract/execute WolframModel calls from notebooks.

## Build & Run

```bash
cd RESEARCHER_BUNDLE

# Build just the Wolfram demos
lake build --wfail wolfram_multiway_demo wolfram_wm148_demo wolfram_roundtrip

# Multiway demos (Lean-only)
lake exe wolfram_multiway_demo -- --sys ce1 --maxDepth 2
lake exe wolfram_wm148_demo -- --maxDepth 2

# Roundtrip echo (requires `wolframscript` on PATH)
lake exe wolfram_roundtrip -- --echo
```

Expected success message for the roundtrip:

```
[echo] Lean→Wolfram→Lean (lossless binary echo)
[echo] OK (byte-identical roundtrip)
```

## End-to-End Verification

The verification script builds the executables, runs the happy paths, and performs robustness checks (missing PATH, missing files):

```bash
cd RESEARCHER_BUNDLE
./scripts/verify_miranda.sh
```

If `wolframscript` is unavailable, the script fails early with a clear message. This makes the WL cross-check mandatory for verification.

## Implementation Notes

- The Lean executables serialize small hypergraphs into a compact binary (little-endian UInt64 list). WL scripts parse the binary and re-emit the same bytes to verify losslessness.
- For WM148, fresh-name handling is explicit and witnessed at the term level. Matching is performed over a finite candidate set of vertex values to keep the demo fully computable.

## Troubleshooting

- “wolframscript not found”: ensure Wolfram Language or WolframScript is installed and on PATH.
- Empty PATH robustness test: the script intentionally clears PATH and expects a non-zero exit; that is a success criterion (no crash).

