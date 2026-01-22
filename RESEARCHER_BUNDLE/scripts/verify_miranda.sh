#!/usr/bin/env bash
set -euo pipefail

echo "=== Miranda Dynamics Verification ==="
echo ""

cd "$(dirname "$0")/.."

ROOTS=(HeytingLean/MirandaDynamics HeytingLean/Bridges HeytingLean/Formal HeytingLean/Tests HeytingLean/WPP HeytingLean/CLI HeytingLean/Util)

echo "Checking for sorry/admit..."
if rg -n --type lean -S "\\b(sorry|admit)\\b" "${ROOTS[@]}" 2>/dev/null; then
  echo "ERROR: Found sorry/admit in codebase"
  exit 1
fi
echo "✓ No sorry/admit found"

echo "Checking for axiom declarations (warning only)..."
if rg -n --type lean -S "^axiom\\b" "${ROOTS[@]}" 2>/dev/null; then
  echo "WARNING: Found axiom declarations (check if intentional)"
else
  echo "✓ No axiom declarations found"
fi

# Speed-up: fetch precompiled `.olean` cache when available (Mathlib v4.x releases).
# Lake does *not* download caches automatically; without this, the first build compiles Mathlib.
echo ""
echo "Fetching Mathlib olean cache (if available)..."
if lake exe cache get; then
  echo "✓ Cache fetched"
else
  echo "WARNING: cache fetch failed; falling back to building from source"
fi

# Build
echo ""
echo "Building project..."
lake build --wfail
echo "✓ Build successful"

echo ""
echo "Building executables (Wolfram cross-check included)..."
lake build --wfail wolfram_roundtrip wolfram_multiway_demo wolfram_wm148_demo
echo "✓ Executables build successful"

echo ""
echo "Building tests (MirandaDynamics AllSanity)..."
lake build --wfail HeytingLean.Tests.MirandaDynamics.AllSanity
echo "✓ Tests build successful"

echo ""
NO_WL=0
if [[ "${1:-}" == "--no-wolfram" ]]; then
  NO_WL=1
fi

if [[ "$NO_WL" -eq 1 ]]; then
  echo "Skipping Wolfram cross-check (--no-wolfram)."
else
  echo "Running Wolfram Language cross-check (mandatory)..."
  if ! command -v wolframscript >/dev/null 2>&1; then
    echo "ERROR: wolframscript not found in PATH (required for cross-check)"
    exit 1
  fi
  lake exe wolfram_roundtrip -- --echo
  echo "✓ Wolfram cross-check passed"
fi

# Count files
echo ""
echo "=== Statistics ==="
lean_files=$(find HeytingLean/MirandaDynamics -name "*.lean" | wc -l)
echo "Lean files: $lean_files"

# Count theorems/lemmas
theorems=$(grep -rh "^theorem\|^lemma" HeytingLean/MirandaDynamics/ 2>/dev/null | wc -l)
echo "Theorems/Lemmas: $theorems"

echo ""
echo "=== All checks passed ==="
