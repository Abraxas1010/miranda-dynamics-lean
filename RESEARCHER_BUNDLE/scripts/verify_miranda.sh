#!/usr/bin/env bash
set -euo pipefail

echo "=== Miranda Dynamics Verification ==="
echo ""

cd "$(dirname "$0")/.."

ROOTS=(HeytingLean/MirandaDynamics HeytingLean/Bridges HeytingLean/Formal HeytingLean/Tests)

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

# Build
echo ""
echo "Building project..."
lake build --wfail
echo "✓ Build successful"

echo ""
echo "Building tests (MirandaDynamics AllSanity)..."
lake build --wfail HeytingLean.Tests.MirandaDynamics.AllSanity
echo "✓ Tests build successful"

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
