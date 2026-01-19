# Research Map: MirandaDynamics integration (2026-01-17)

This note is the “evidence + mapping” record required by `AGENTS.md` before extending the
Miranda/TKFT/billiards/fluids layer with new mathematical content.

## 0) Scope (what this repo does / does not claim)

**Mechanized here (Lean, no `sorry`, no new axioms):**
- An abstract **TKFT-style reaching relation** `α ↝ β`, its relational composition laws, and a principled
  upgrade to a `Part` when outputs are unique.
- A **periodic/loop nucleus spine** (“union nucleus”) and specializations used by other parts of the repo.
- A fully **discrete end-to-end reduction**: halting (Mathlib’s `Nat.Partrec.Code`) ↔ reaching a period-2 orbit,
  plus the undecidability transfer consequence.
- A mathematically meaningful **Cantor-set tape encoding spine** (Cantor-function injectivity + head-position
  interval embeddings), sufficient to ground part of the Miranda–Ramos “billiards compute” story in Lean,
  without formalizing billiard geometry.

**Not re-proved here (external mathematics, cited but not axiomatized in Lean):**
- The geometric/PDE constructions in the Miranda/Peralta-Salas ecosystem (TKFT clean dynamical bordisms,
  billiard tables with reflection laws, Euler/Navier–Stokes steady states).

## 1) External sources (ground truth from the literature)

These are the primary references used to align terminology and avoid overstating mechanization.

- TKFT: González-Prieto, Miranda, Peralta-Salas, “Topological Kleene Field Theories as a model of computation”.
  - arXiv:2503.16100 (Mar 2025): `https://arxiv.org/abs/2503.16100`
- Billiards: Miranda, Ramos, “Classical billiards can compute”.
  - arXiv:2512.19156 (Dec 2025): `https://arxiv.org/abs/2512.19156`
- Euler flows: Cardona, Miranda, Peralta-Salas, Presas, “Universality of Euler flows and flexibility of Reeb embeddings”.
  - arXiv:1911.01963 (Nov 2019): `https://arxiv.org/abs/1911.01963`
  - Published account (PNAS): “Constructing Turing complete Euler flows in dimension 3” (PNAS 118(19):e2026818118).
    - PNAS landing page: `https://www.pnas.org/doi/10.1073/pnas.2026818118`
- Navier–Stokes steady states (bibliography tracking):
  - Dyhr, González-Prieto, Miranda, Peralta-Salas, “Turing complete Navier-Stokes steady states via cosymplectic geometry”.
    - arXiv:2507.07696 (Jul 2025): `https://arxiv.org/abs/2507.07696`
    - Evidence (author page listing): `https://muckrack.com/r/devryhr/bio`
  - Related (also cosymplectic, but a *different* title): Dyhr, “Turing complete Reeb flows and the cosymplectic Chern-Hamilton conjecture”.
    - arXiv:2505.10379 (May 2025): `https://arxiv.org/abs/2505.10379`

## 2) Internal codebase mapping (Lean identifiers + reuse targets)

### 2.1 TKFT reaching relations (the semantics spine)

- `lean/HeytingLean/MirandaDynamics/TKFT/Reaching.lean`
  - `HeytingLean.MirandaDynamics.TKFT.ReachingRel`
  - `HeytingLean.MirandaDynamics.TKFT.ReachingRel.comp`
  - `HeytingLean.MirandaDynamics.TKFT.ReachingRel.id_left`
  - `HeytingLean.MirandaDynamics.TKFT.ReachingRel.assoc`
  - `HeytingLean.MirandaDynamics.TKFT.ReachingRel.Image`
  - `HeytingLean.MirandaDynamics.TKFT.ReachingRel.toPart`

- `lean/HeytingLean/MirandaDynamics/TKFT/Category.lean`
  - `HeytingLean.MirandaDynamics.TKFT.Obj`
  - `CategoryTheory.Category HeytingLean.MirandaDynamics.TKFT.Obj` (reaching relations as morphisms)

### 2.1c Flow-induced reaching relations (Mathlib `Flow` integration)

- `lean/HeytingLean/MirandaDynamics/TKFT/FlowReaching.lean`
  - `HeytingLean.MirandaDynamics.TKFT.reachingRelOfFlow`
  - `HeytingLean.MirandaDynamics.TKFT.reachingRelOfFlow_comp`

### 2.1d Category bridge (reuse Mathlib’s `RelCat`)

- `lean/HeytingLean/MirandaDynamics/TKFT/RelCatBridge.lean`
  - `HeytingLean.MirandaDynamics.TKFT.RelCatBridge.equivalence`

### 2.1b External-claim packaging (named wrappers; still no axioms)

- `lean/HeytingLean/MirandaDynamics/External/Claims.lean`
  - `HeytingLean.MirandaDynamics.External.BilliardsComputesClaim`
  - `HeytingLean.MirandaDynamics.External.EulerTuringCompleteClaim`
  - `HeytingLean.MirandaDynamics.External.NavierStokesTuringCompleteClaim`
- `lean/HeytingLean/MirandaDynamics/External/Consequences.lean`
  - `HeytingLean.MirandaDynamics.External.not_computable_of_billiardsComputes`

### 2.2 Fixed-point / nucleus spine (“periodic closure” model)

- `lean/HeytingLean/MirandaDynamics/FixedPoint/PeriodicNucleus.lean`
  - `HeytingLean.MirandaDynamics.FixedPoint.unionNucleus`
  - `HeytingLean.MirandaDynamics.FixedPoint.isFixedPoint_unionNucleus_iff`

### 2.3 Discrete halting ↔ periodic-orbit bridge (end-to-end in Lean)

- `lean/HeytingLean/MirandaDynamics/Discrete/HaltingToPeriodic.lean`
  - `HeytingLean.MirandaDynamics.Discrete.reachesPeriod2_iff_halts`
  - `HeytingLean.MirandaDynamics.Discrete.haltingReducesToReachesPeriod2`
  - `HeytingLean.MirandaDynamics.Discrete.not_computable_reachesPeriod2`

### 2.3b Discrete flow + TKFT reaching bridge (end-to-end in Lean)

- `lean/HeytingLean/MirandaDynamics/Discrete/FlowBridge.lean`
  - `HeytingLean.MirandaDynamics.Discrete.stepFlow`
  - `HeytingLean.MirandaDynamics.Discrete.ReachesCycle`
  - `HeytingLean.MirandaDynamics.Discrete.reachesCycle_iff_halts`
  - `HeytingLean.MirandaDynamics.Discrete.reachingRel_cycle`

- `lean/HeytingLean/MirandaDynamics/Undecidability/Transfers.lean`
  - `HeytingLean.MirandaDynamics.Undecidability.ManyOne.not_computable_of_reduces`
  - `HeytingLean.MirandaDynamics.Undecidability.Halting.not_computable_of_halting_reduces`

### 2.4 Billiards (Cantor encoding + head position embedding, not billiard geometry)

- `lean/HeytingLean/MirandaDynamics/Billiards/CantorEncoding.lean`
  - `HeytingLean.MirandaDynamics.Billiards.encodeTape`
  - `HeytingLean.MirandaDynamics.Billiards.encodeTape_injective`
  - `HeytingLean.MirandaDynamics.Billiards.tau` / `headInterval` / `headInterval_disjoint`
  - `HeytingLean.MirandaDynamics.Billiards.encodeWithHead_shift`
  - `HeytingLean.MirandaDynamics.Billiards.encodeWithHead_injective_pair`

- `lean/HeytingLean/MirandaDynamics/Billiards/CantorNucleus.lean`
  - `HeytingLean.MirandaDynamics.Billiards.cantorNucleus`
  - `HeytingLean.MirandaDynamics.Billiards.cantorNucleus_fixed_iff`

## 3) Executables + regression tests (executable-first contract)

Executables (Lean `lean_exe` targets; see `lean/lakefile.lean`):
- `miranda_dynamics_demo` (root: `HeytingLean.MirandaDynamics.DemoMain`)
- `miranda_billiards_demo` (root: `HeytingLean.MirandaDynamics.Billiards.DemoMain`)
- `miranda_discrete_demo` (root: `HeytingLean.MirandaDynamics.Discrete.DemoMain`)

Tests:
- `lean/HeytingLean/Tests/MirandaDynamics/Sanity.lean`
- `lean/HeytingLean/Tests/MirandaDynamics/BilliardsSanity.lean`
- `lean/HeytingLean/Tests/MirandaDynamics/DiscreteSanity.lean`
- `lean/HeytingLean/Tests/MirandaDynamics/DiscreteFlowSanity.lean`
- `lean/HeytingLean/Tests/MirandaDynamics/FluidsSanity.lean`

## 4) Open gaps → proposed next research tasks

1. **Interfaces for “external realization”** (low risk, high clarity)
   - Add more granular interfaces capturing: “a flow/billiard realizes a reaching relation” and
     “a geometric construction provides a many-one reduction from halting to predicate `P`”.
   - Status: partially addressed by `External/Claims` and `External/Consequences`; “realizes reaching
     relation” remains an open interface target.
2. **Strengthen the Cantor/billiards bridge** (moderate)
   - Formalize additional purely-analytic lemmas from Miranda–Ramos that do not require billiard geometry.
3. **Unification statement (hypothesis-first)** (moderate)
   - State a “Heyting–Turing correspondence” theorem only at the abstract nucleus/kernel level already
     present in the repo, with explicit hypotheses, leaving geometry as external evidence.
