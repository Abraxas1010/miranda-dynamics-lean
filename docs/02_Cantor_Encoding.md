# Cantor Tape Encoding

## Overview

The Cantor encoding is the key bridge between Turing machines and billiard dynamics.
It maps bi-infinite binary tapes to points in the ternary Cantor set, allowing
symbolic computation to be represented geometrically.

## The Encoding

A Turing machine tape `(tape : ℤ → Bool)` is encoded as a real number in [0,1]:

```lean
def encodeTape (tape : ℤ → Bool) : ℝ := ∑' n, (2 * tape n.1) / 3^(n.1 + 1)
```

Where the sum ranges over positive integers, encoding both left and right halves
of the bi-infinite tape.

## Key Theorem: Injectivity

```lean
theorem encodeTape_injective : Function.Injective encodeTape
```

**Interpretation**: Different tapes map to different points. No information is lost
in the geometric encoding.

## Head Position Embedding

The tape head position `k : ℤ` is encoded via an affine map τ_k that shifts the
Cantor set embedding:

```lean
def headInterval (k : ℤ) : Set ℝ := Icc (k : ℝ) (k + 1)
def τ (k : ℤ) (x : ℝ) : ℝ := x + k
```

## Nucleus Structure

The Cantor encoding induces a nucleus (closure operator) on sets:

```lean
def cantorNucleus : Nucleus (Set ℝ) := ...
```

Fixed points of this nucleus correspond to symbolically invariant sets.

## Connection to Billiards

In Miranda-Ramos billiard construction:
1. The Cantor set lives on a wall of the billiard table
2. Collision angles encode tape symbols
3. Table geometry enforces Turing machine transitions

## Files

| File | Contents |
|------|----------|
| `Billiards/CantorEncoding.lean` | Core encoding and injectivity |
| `Billiards/CantorNucleus.lean` | Nucleus operator |
| `Billiards/CantorTapeUpdate.lean` | Write operations |
| `Billiards/CantorDigits.lean` | Digit stream indexing |
| `Billiards/CantorCylinders.lean` | Cylinder set machinery |

## References

- Miranda, E., & Ramos, D. (2025). *Classical billiards can compute*. arXiv:2512.19156, Section 3
