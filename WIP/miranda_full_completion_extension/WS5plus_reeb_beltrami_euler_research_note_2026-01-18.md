# WS5+ Research Note (Reeb/Beltrami/Euler track) — 2026-01-18

## Goal (long-horizon)
Mechanize the “realization” direction of the Miranda pipeline:

`generalized shift / symbolic dynamics` → `billiards / contact / Beltrami / steady Euler` (and later NS).

This repo currently treats the Euler/NS universality theorems as **external claims** (data-only wrappers)
and focuses on fully mechanizing the *reduction logic downstream*.

## What is now fully mechanized (new stepping stone)

### Generalized shift + periodic-orbit predicate (internal)
- `lean/HeytingLean/MirandaDynamics/Computation/GeneralizedShift.lean`
- `lean/HeytingLean/MirandaDynamics/Computation/GeneralizedShiftPeriodic.lean`
- `lean/HeytingLean/MirandaDynamics/Discrete/GeneralizedShiftBridge.lean`

Key result: the discrete halting ↔ reach-a-period-2-orbit predicate is transported into the generalized
shift embedding, so the analytic “realization” work can target:

`Discrete.ShiftPeriodic.ReachesPeriod2Shift n c`

instead of targeting the halting problem directly.

Additionally, `ReachesPeriod2Shift` is proved non-computable on `Code` (many-one reduction with `id`):
- `Discrete.ShiftPeriodic.haltingReducesToReachesPeriod2Shift`
- `Discrete.ShiftPeriodic.not_computable_reachesPeriod2Shift`

## Local codebase inventory (already present)

### Contact/Reeb (staged)
- Pointwise Reeb equations and uniqueness lemma:
  - `lean/HeytingLean/MirandaDynamics/Geometry/Contact/Euclidean.lean`
- A linear “Reeb-style” package and constant-velocity flow:
  - `lean/HeytingLean/MirandaDynamics/Fluids/ContactLinear.lean`
  - `lean/HeytingLean/MirandaDynamics/Fluids/ContactLinearFlow.lean`

### Beltrami + steady Euler shell (staged)
- A lightweight `curl` wrapper and Beltrami predicate:
  - `lean/HeytingLean/MirandaDynamics/Fluids/VectorCalculus/Curl3.lean`
- A steady Euler (Bernoulli/Lamb form) shell and “Beltrami ⇒ steady Euler” lemma:
  - `lean/HeytingLean/MirandaDynamics/Fluids/VectorCalculus/GradDiv3.lean`

### External boundary (data-only)
- Named wrappers for “Euler steady flows are Turing complete”, “Navier–Stokes steady states are Turing complete”:
  - `lean/HeytingLean/MirandaDynamics/External/Claims.lean`
- Consequences (non-computability transfer) from those wrappers:
  - `lean/HeytingLean/MirandaDynamics/External/Consequences.lean`

## External references located (non-verified in Lean)

### Reeb definition (for provenance)
- Wikipedia: “Reeb vector field” — definition `α(R)=1` and `dα(R,·)=0`:
  - https://en.wikipedia.org/wiki/Reeb_vector_field
- Wikipedia: “Contact geometry” — Reeb section in Darboux coordinates:
  - https://en.wikipedia.org/wiki/Contact_geometry
- Lean/Mathlib overview page (coverage + pointers):
  - https://lean-lang.org/use-cases/mathlib

## Search outcome (verified formalizations)
Web searches performed (2026-01-18):
- “mathlib Reeb vector field”
- “Lean theorem prover Beltrami field curl formalization”
- “Lean theorem prover incompressible Euler equations formalization”
- “mathlib Navier-Stokes formalization Lean”

Result: no obvious, authoritative Lean/mathlib formalization of the *Euler equations* / *Navier–Stokes*
or a turnkey `curl`-based Beltrami PDE development surfaced from those queries.

Given that gap, the current approach in this repo (staged “shell” predicates + external-claim boundary)
remains the pragmatic path.

## Next mechanizable subgoals (proposed)

1) **Define a realization interface (data-only, no axioms)** from a generalized shift to a flow:
   - a manifold/state space `X`
   - a (partial) flow or time-`1` map `Φ : X → X`
   - an encoding `enc : GenShiftCfg α → X` and simulation lemma `enc (step s) = Φ (enc s)`

   Implemented (minimal deterministic version):
   - `lean/HeytingLean/MirandaDynamics/Computation/FlowRealization.lean`

2) Add *staged* constraints connecting `Φ` to the Reeb/Beltrami/Euler shells:
   - e.g. `Φ` induced by a vector field `u`, plus `IsBeltrami u λ` or `IsEulerSteadyBernoulli u p`.

3) Use (1)+(2) to transport undecidability from `ReachesPeriod2Shift` to a “steady Euler predicate”
   that matches the interface in `External/Interfaces.lean`, without claiming any analytic existence theorem.
