# TKFT: Topological Kleene Field Theory

## Overview

TKFT (Topological Kleene Field Theory) provides the categorical foundation for understanding
dynamical systems as computational devices. Developed by González-Prieto, Miranda, and
Peralta-Salas, it unifies various "X is Turing-complete" results under a single framework.

## Core Concept: Reaching Relations

A **reaching relation** captures when one state can evolve to another through dynamics:

```lean
structure ReachingRel (X Y : Type*) where
  rel : X → Y → Prop
```

Key properties (mechanized in `TKFT/Reaching.lean`):
- **Composition**: `(r ∘ᵣ s) x z ↔ ∃ y, r x y ∧ s y z`
- **Identity**: `id x y ↔ x = y`
- **Associativity**: `(r ∘ᵣ s) ∘ᵣ t = r ∘ᵣ (s ∘ᵣ t)`

## Categorical Structure

Reaching relations form a category (`TKFT/Category.lean`):
- **Objects**: Types (state spaces)
- **Morphisms**: Reaching relations
- **Composition**: Relational composition

This is equivalent to Mathlib's `CategoryTheory.RelCat` (`TKFT/RelCatBridge.lean`).

## Bordism Semantics

TKFT interprets computation through bordisms:
- **States** = boundary conditions
- **Computations** = bordisms between boundaries
- **Composition** = gluing bordisms

See `TKFT/BordismSemantics.lean` and `TKFT/DiscreteBordism.lean`.

## Mathlib Integration

`TKFT/FlowReaching.lean` shows how Mathlib's `Flow` objects induce reaching relations:

```lean
def reachingRelOfFlow (φ : Flow M α) : ReachingRel α α where
  rel x y := ∃ t : ℝ, t ≥ 0 ∧ φ.toFun t x = y
```

## Key Theorems

| Theorem | Location | Statement |
|---------|----------|-----------|
| `ReachingRel.assoc` | `TKFT/Reaching.lean` | Composition is associative |
| `ReachingRel.id_left` | `TKFT/Reaching.lean` | Identity law |
| `equivalence` | `TKFT/RelCatBridge.lean` | TKFT ≃ RelCat |

## References

- González-Prieto, Á., Miranda, E., & Peralta-Salas, D. (2025). *Topological Kleene Field Theories as a model of computation*. arXiv:2503.16100
