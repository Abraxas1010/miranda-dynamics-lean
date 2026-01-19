#!/usr/bin/env bash
set -euo pipefail

echo "=== Miranda Dynamics Verification ==="
echo ""

cd "$(dirname "$0")/.."

# Check for sorry
echo "Checking for sorry..."
if grep -rn "sorry" HeytingLean/MirandaDynamics/ HeytingLean/Bridges/ HeytingLean/Formal/ 2>/dev/null; then
    echo "ERROR: Found sorry in codebase"
    exit 1
fi
echo "✓ No sorry found"

# Check for admit
echo "Checking for admit..."
if grep -rn "admit" HeytingLean/MirandaDynamics/ HeytingLean/Bridges/ HeytingLean/Formal/ 2>/dev/null; then
    echo "ERROR: Found admit in codebase"
    exit 1
fi
echo "✓ No admit found"

# Check for axiom (warning only)
echo "Checking for axiom declarations..."
if grep -rn "^axiom " HeytingLean/MirandaDynamics/ HeytingLean/Bridges/ HeytingLean/Formal/ 2>/dev/null; then
    echo "WARNING: Found axiom declarations (check if intentional)"
else
    echo "✓ No axiom declarations found"
fi

# Build
echo ""
echo "Building project..."
lake build --wfail
echo "✓ Build successful"

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
