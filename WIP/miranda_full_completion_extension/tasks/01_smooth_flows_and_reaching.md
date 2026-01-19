# WS1 Tasks: Smooth flows & reaching semantics (2026-01-17)

## Goal

Build a **reusable, proof-grade bridge** from Mathlib’s ODE / integral-curve machinery to the existing
MirandaDynamics reaching-relation semantics, so later geometry (contact / billiards / PDE) can express:

> “this dynamical system induces a reaching relation”  
> and “gluing/time-addition corresponds to relational composition”

without relying on axioms.

## Why this is a first workstream

- Mathlib already provides strong foundations for ODE existence/uniqueness and manifold integral curves.
- The current MirandaDynamics spine already has:
  - a reaching-relation category (`TKFT.Obj`),
  - a flow-to-reaching map for **global** flows (`TKFT.reachingRelOfFlow`).

The missing piece is a **partial/local flow** story compatible with ODEs on manifolds.

## Inputs (existing assets to reuse)

### In this repo
- `lean/HeytingLean/MirandaDynamics/TKFT/FlowReaching.lean`
  - `TKFT.reachingRelOfFlow` (global `Flow τ α`)
  - `TKFT.reachingRelOfFlow_comp` (composition via `Flow.map_add`)

### In Mathlib (internal modules)
- `Mathlib/Analysis/ODE/PicardLindelof.lean`
  - existence of local solutions and *local flows* (as functions with neighborhood domains)
- `Mathlib/Geometry/Manifold/IntegralCurve/ExistUnique.lean`
  - existence/uniqueness of integral curves on manifolds

## External search notes (links)
- Mathlib docs:
  - Picard–Lindelöf: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/ODE/PicardLindelof.html
  - Manifold integral curves: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/IntegralCurve/ExistUnique.html

## What’s missing / “no turnkey solution”

Mathlib provides theorems that *imply* local flows, but not a single, project-facing abstraction matching:

```lean
-- desired: a partial flow with a domain predicate
structure PartialFlow (τ α) :=
  (dom : τ → α → Prop)
  (map : ∀ t x, dom t x → α)
  (map_zero : ...)
  (map_add : ...)
```

So this WS builds a packaging layer and proves the minimal algebraic laws needed for reaching semantics.

## Task list (decomposed)

### WS1.1 Internal search: locate existing “local flow” structures (Research-needed → then Moderate)

- [x] Search Mathlib for any existing structure/typeclass capturing local flow composition laws
      (beyond the existential statements in Picard–Lindelöf).
  - Commands:
    - `rg -n "structure.*Flow|LocalFlow|PartialFlow" lean/.lake/packages/mathlib/Mathlib -S`
    - `python3 scripts/mathlib_search.py --moogle "local flow structure"`
- [ ] If an existing structure exists:
  - [ ] Adopt it and write a tiny adapter to `TKFT.ReachingRel`.
- [x] If not:
  - [x] Define a small `PartialFlow` in `HeytingLean.MirandaDynamics` with just the laws we need.

**Acceptance:** a short note in this file summarizing what was found and chosen.

Outcome (2026-01-17): no standalone `LocalFlow`/`PartialFlow` structure was found in Mathlib;
Picard–Lindelöf phrases “local flow” as a function with domain theorems rather than a dedicated bundled
algebraic interface. We therefore introduced a small project-local `Dynamics.PartialFlow` and proved the
partial-flow reaching composition lemma.

### WS1.2 Define `PartialFlow` (Moderate)

- [x] Add `lean/HeytingLean/MirandaDynamics/Dynamics/PartialFlow.lean` with:
  - `dom : τ → α → Prop`
  - `map : ∀ t x, dom t x → α`
  - `map_zero` and `map_add` laws with domain side-conditions
  - simp lemmas and minimal API

**Acceptance:** `lake build --wfail` passes and a small example compiles.

### WS1.3 Partial-flow reaching relation (Moderate)

- [x] Add `lean/HeytingLean/MirandaDynamics/TKFT/PartialFlowReaching.lean`:
  - define `reachingRelOfPartialFlow` between subsets `In Out`
  - statement: `x ↝ y` iff `∃ t, dom t x ∧ map t x = y`
  - prove a composition lemma (time-addition style) under appropriate domain hypotheses

**Acceptance:** lemma analogous to `reachingRelOfFlow_comp` (but with domain conditions) with no linter warnings.

### WS1.4 “Lift” Mathlib ODE local flows into `PartialFlow` (Research-needed → Complex)

Goal: take the output of Picard–Lindelöf (local flow as a function on a neighborhood) and package it as
`PartialFlow` on an explicit domain.

- [ ] Decide: normed-space first, then manifolds; or manifolds directly.
  - default: start on normed spaces `E` using Picard–Lindelöf, then generalize.
- [ ] Build `PartialFlow` instance for a `C¹` vector field near a point with:
  - `dom t x := (x,t) in some neighborhood` (explicit sets like `closedBall × Ioo` or similar)
  - `map t x := α x t` from the theorem
  - prove `map_zero` (initial condition) and `map_add` where it holds (this is the hard part)

**Acceptance:** a first “toy” `PartialFlow` derived from Picard–Lindelöf with a *usable* `map_zero`, and a
documented plan for `map_add` (which may require uniqueness+patching arguments).

### WS1.5 Executable smoke test (Moderate)

- [x] Add a small `lean_exe` demo:
  - constructs a simple ODE local flow (e.g. `x' = 1` on `ℝ`)
  - prints a few reachable pairs (time steps) and exits 0
- [x] Ensure it runs under hostile env:
  - `env -i PATH="" lake exe <name> ...` (or direct binary)

**Acceptance:** demo binary builds and runs; robustness scripts do not crash.

## QA protocol (incremental)

- Dev: `./scripts/qa_dev.sh --modules HeytingLean.MirandaDynamics`
- After adding a new executable: build+run affected exes + `./scripts/qa_robustness_affected.sh`

## Progress log

- 2026-01-17:
  - Landed a minimal `PartialFlow` abstraction in `lean/HeytingLean/MirandaDynamics/Dynamics/PartialFlow.lean`.
  - Added partial-flow reaching semantics + composition lemma in `lean/HeytingLean/MirandaDynamics/TKFT/PartialFlowReaching.lean`.
  - Added proof-level sanity check `lean/HeytingLean/Tests/MirandaDynamics/PartialFlowSanity.lean`.
  - Added executable `miranda_partialflow_demo`:
    - `lean/HeytingLean/MirandaDynamics/Dynamics/PartialFlowDemoMain.lean`
    - Verified happy path + hostile env: `env -i PATH="" ./lean/.lake/build/bin/miranda_partialflow_demo`.

Note: the demo currently uses an explicit algebraic partial flow (`x ↦ x + t` on `Nat`) rather than
deriving a local flow from Picard–Lindelöf. Lifting Mathlib’s ODE local-flow theorems into a bundled
`PartialFlow` remains WS1.4 (the hard, research-heavy step).
