# Backlog: “Full Miranda/TKFT/Billiards/Fluids Formalization” (2026-01-17)

This backlog is the remaining work needed to make the Miranda/TKFT/billiards/Euler/Navier–Stokes
claims **fully mechanized in Lean** (rather than cited externally via interfaces).

It exists because the current plan (`WIP/miranda_integration_plan.md`) is intentionally scoped to a
Lean-realistic spine. “Full completion” is a multi-quarter (likely multi-year) effort.

Project-extension decomposition (more detailed workstream task lists):
- `WIP/miranda_full_completion_extension/00_overview.md`
- `WIP/miranda_full_completion_extension/00_research_map_2026-01-17.md`

## 0) Current state (what is already mechanized)

See:
- `WIP/miranda_integration.md` (status banner with concrete files)
- `WIP/miranda_research_map_2026-01-17.md` (citations + internal mapping)

Additional milestone (2026-01-17):
- The discrete halting model now also integrates with Mathlib’s `Flow` abstraction and the TKFT-style
  reaching relation (`reachingRelOfFlow`): `lean/HeytingLean/MirandaDynamics/Discrete/FlowBridge.lean`.

## 1) Internal search results (Mathlib/Lean feasibility check)

Quick scans of Mathlib in this repo found **no existing library** for:
- contact geometry / Reeb vector fields (`Contact`, `Reeb`)
- Beltrami fields (`Beltrami`)
- cosymplectic geometry (`cosymplectic`)

So “full completion” requires building a substantial new formalization layer (or importing it from
elsewhere, if it exists).

Note: Mathlib *does* provide substantial ODE and integral-curve infrastructure (Picard–Lindelöf, manifold
integral curves). The missing piece for this project is a project-facing **partial-flow packaging** that
connects those results to the existing reaching-relation semantics.

## 2) External search results (verified formalizations)

I did not find an existing, ready-to-reuse Lean formalization of:
- TKFT “clean dynamical bordisms” and reaching functions,
- Miranda–Ramos billiard geometry with reflection law + Cantor encoding,
- the Euler / Navier–Stokes Turing completeness constructions.

This should be revisited periodically, but the current working assumption is: **we must build it**.

## 3) Decomposition (minimal dependency chain)

### Phase 1 — Foundations (weeks)

1. **ODE/flow layer (smooth dynamics)**
   - Goal: define a reusable notion of flow for a (smooth) vector field and basic properties needed
     for “reaching time” style semantics.
   - Likely dependencies: Mathlib manifold + analysis libraries; investigate existing `Flow`/`IsClosed` APIs.
   - Status: discrete-time flow abstraction now used directly in the discrete halting model via
     `Flow.fromIter` (no ODE yet).

2. **Contact geometry layer (definition-first)**
   - Goal: define contact form, Reeb vector field, and basic lemmas (existence/uniqueness under
     hypotheses).
   - Current starter: `lean/HeytingLean/MirandaDynamics/Fluids/ContactLinear.lean` (linear spine).
   - Next: upgrade from linear-algebra “contact-like data” to tangent-space local definitions on
     manifolds (still without global theorems).

3. **Cosymplectic layer (definition-first)**
   - Goal: define cosymplectic structures and the geometric objects referenced by the Navier–Stokes
     universality preprint.

### Phase 2 — TKFT (months)

4. **Define “clean dynamical bordism”**
   - Goal: a Lean definition that matches the paper’s hypotheses tightly enough to state and prove:
     - gluing composition law,
     - “reaching relation” induced by the bordism.
   - Approach: start with a *discrete* or *PL* model and refine.

5. **Reaching function semantics (no choice)**
   - Goal: a constructive formulation replacing `Classical.choose` with explicit witnesses in the
     “output-on-image” sense, aligning to `TKFT.ReachingRel.Image`.

### Phase 3 — Billiards (months to year)

6. **Formal billiard table + reflection law**
   - Goal: define piecewise-smooth boundary, specular reflection, and trajectory evolution.

7. **Cantor encoding integration**
   - Goal: connect billiard geometry modules to the already mechanized Cantor encoding spine:
     `lean/HeytingLean/MirandaDynamics/Billiards/CantorEncoding.lean`.

8. **Halting ↔ periodicity reduction**
   - Goal: state and prove the many-one reduction in Lean, then derive non-computability via
     `Undecidability/Transfers`.

### Phase 4 — Fluids (year+)

9. **Beltrami ↔ Reeb (Etnyre–Ghrist bridge)**
   - Goal: formalize the differential-topological bridge used by Euler universality constructions.

10. **Euler steady-state universality construction**
   - Goal: formalize the encoding construction and prove the reduction to a dynamical predicate.

11. **Navier–Stokes steady-state universality construction**
   - Goal: formalize cosymplectic geometry + the encoding construction and prove the reduction.

## 4) How to keep this honest during the long haul

Use the existing pattern:
- Put theorems we *can prove* in Lean under `HeytingLean.MirandaDynamics.*`.
- Keep “literature claims” as explicit interfaces:
  - `lean/HeytingLean/MirandaDynamics/External/Interfaces.lean`
  - `lean/HeytingLean/MirandaDynamics/External/Claims.lean`
  - `lean/HeytingLean/MirandaDynamics/External/Consequences.lean`

Then, as each geometric/PDE piece becomes mechanized, move it from “External” into the main namespace
and delete the corresponding interface usage.
