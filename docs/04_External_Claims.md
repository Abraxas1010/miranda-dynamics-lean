# External Claims: Honest Boundaries

## Philosophy

This formalization is honest about what it proves vs. what it assumes.

**Mechanized** (no axioms, no sorry): Abstract categorical structure, encodings,
discrete bridges, undecidability transfers.

**External claims** (interfaces): Geometric content from the physics papers that
would require substantial additional machinery (contact geometry, PDEs, etc.).

## Interface Pattern

External claims are represented as **type structures**, not axioms:

```lean
-- Current mechanized interface (see `RESEARCHER_BUNDLE/HeytingLean/MirandaDynamics/External/Claims.lean`):
--
-- A named wrapper for “billiards can compute” used only through an undecidability reduction.
structure BilliardsComputesClaim (β : Type u) [Primcodable β] (n : ℕ) (Periodic : β → Prop) : Type (u + 1) where
  haltingToPeriodic : HaltingToPredicate (β := β) n Periodic
```

**Key principle**: No `axiom` declarations. The claim is a **type** that can
be instantiated if someone provides the geometric proofs.

**Note:** earlier versions of this document used a more “geometric” schematic interface
(`table`, `encode`, `step_corresponds`, …). The current codebase keeps the boundary *minimal*:
it only assumes the ingredient actually consumed downstream—an explicit many-one reduction from
halting to a physical predicate—so that the kernel story stays clean while remaining usable.

## Current Claims

### BilliardsComputesClaim

From Miranda-Ramos (2025): A 2D polygonal billiard table can simulate any TM.

**What's mechanized**: Cantor encoding, head position intervals
**What's external**: Table geometry, collision mechanics, return map proofs

### EulerTuringCompleteClaim

From Cardona et al. (2021): Steady Euler flows on S³ are Turing-complete.

**What's mechanized**: TKFT framework, halting ↔ periodic
**What's external**: Beltrami field construction, contact geometry, Etnyre-Ghrist

### NavierStokesTuringCompleteClaim

From Dyhr et al. (2025): Viscosity doesn't break universality.

**What's mechanized**: Same as Euler
**What's external**: Cosymplectic geometry, harmonic field analysis

## Using External Claims

Theorems can depend on claims explicitly:

```lean
theorem not_computable_of_billiardsComputes
    (claim : BilliardsComputesClaim β n Periodic) : ¬ComputablePred Periodic := ...
```

The dependency on `claim` is visible in the type signature.

## Files

| File | Contents |
|------|----------|
| `External/Interfaces.lean` | Abstract claim structures |
| `External/Claims.lean` | Named claim wrappers |
| `External/Consequences.lean` | Theorems consuming claims |

## Future Work

As geometric content is formalized:
1. Instantiate the claim structures
2. Remove the explicit claim parameters
3. The theorems become unconditionally mechanized

This is the **incremental formalization** approach: prove what you can,
make explicit what you assume.
