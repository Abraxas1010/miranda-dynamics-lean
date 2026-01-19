# HeytingLean × MirandaDynamics — Implementation Plan (2026-01-18)

This plan converts `WIP/miranda_integration.md` into an actionable, Lean-realistic roadmap that follows:
- `AGENTS.md` (executable-first QA, incremental builds, hostile-env checks, no CI config changes),
- the `problem-solving` skill (search-first + documented research trail).

For the required “evidence + mapping” note, see: `WIP/miranda_research_map_2026-01-17.md`.

For the “full completion” project extension (mechanizing geometry/PDE claims, not just the Lean spine), see:
- `WIP/miranda_full_completion_extension/00_overview.md`
- `WIP/miranda_full_completion_extension/00_research_map_2026-01-17.md`

## 1) Definition of Done (for the “Miranda integration” spine)

**DONE means:**
1. `lean/HeytingLean/MirandaDynamics/**` builds with strict flags (no `sorry`, warnings-as-errors).
2. All Miranda `lean_exe` targets build and run successfully (happy path).
3. Hostile environment runs do not crash (empty env / minimal `PATH`).
4. Documentation is truthful: “mechanized vs planned” is clearly separated, and references match files.
5. The sub-book inventory points to the correct docs/plan files.

## 2) Current deliverables (already in the repo)

### 2.1 Lean modules (mechanized; no new axioms)

- Umbrella:
  - `lean/HeytingLean/MirandaDynamics.lean`
- TKFT reaching-rel semantics:
  - `lean/HeytingLean/MirandaDynamics/TKFT/Reaching.lean`
  - `lean/HeytingLean/MirandaDynamics/TKFT/Category.lean`
  - `lean/HeytingLean/MirandaDynamics/TKFT/FlowReaching.lean`
  - `lean/HeytingLean/MirandaDynamics/TKFT/RelCatBridge.lean`
- Fixed-point / nucleus spine:
  - `lean/HeytingLean/MirandaDynamics/FixedPoint/PeriodicNucleus.lean`
- Undecidability transfer + discrete end-to-end bridge:
  - `lean/HeytingLean/MirandaDynamics/Undecidability/Transfers.lean`
  - `lean/HeytingLean/MirandaDynamics/Discrete/HaltingToPeriodic.lean`
  - `lean/HeytingLean/MirandaDynamics/Discrete/FlowBridge.lean`
  - `lean/HeytingLean/MirandaDynamics/Discrete/GeneralizedShiftBridge.lean`
- External-results boundary (interfaces, not axioms):
  - `lean/HeytingLean/MirandaDynamics/External/Interfaces.lean`
  - `lean/HeytingLean/MirandaDynamics/External/Claims.lean`
  - `lean/HeytingLean/MirandaDynamics/External/Consequences.lean`
- Billiards (analytic Cantor encoding spine; not billiard geometry):
  - `lean/HeytingLean/MirandaDynamics/Billiards/CantorEncoding.lean`
  - `lean/HeytingLean/MirandaDynamics/Billiards/CantorNucleus.lean`
  - `lean/HeytingLean/MirandaDynamics/Billiards/CantorTapeUpdate.lean`
  - `lean/HeytingLean/MirandaDynamics/Billiards/PaperMap.lean`
  - `lean/HeytingLean/MirandaDynamics/Billiards/PaperMapFull.lean`
- Heyting–Turing (hypothesis-first correspondence spine):
  - `lean/HeytingLean/MirandaDynamics/HeytingTuring/Correspondence.lean`
- Additional supporting tracks:
  - `lean/HeytingLean/MirandaDynamics/Computation/FlowRealization.lean`
  - `lean/HeytingLean/MirandaDynamics/Computation/GeneralizedShift.lean`
  - `lean/HeytingLean/MirandaDynamics/Computation/GeneralizedShiftPeriodic.lean`
  - `lean/HeytingLean/MirandaDynamics/Topology/BettiComplexity.lean`
  - `lean/HeytingLean/MirandaDynamics/Fluids/ContactLinear.lean` (linear spine; no PDE)

### 2.2 Executables (must build + run)

In `lean/lakefile.lean`:
- `miranda_dynamics_demo`
- `miranda_billiards_demo`
- `miranda_billiards_geometry_demo`
- `miranda_discrete_demo`
- `miranda_partialflow_demo`

### 2.3 Tests

- `lean/HeytingLean/Tests/MirandaDynamics/Sanity.lean`
- `lean/HeytingLean/Tests/MirandaDynamics/BilliardsSanity.lean`
- `lean/HeytingLean/Tests/MirandaDynamics/DiscreteSanity.lean`
- `lean/HeytingLean/Tests/MirandaDynamics/TKFTBordismSanity.lean`
- `lean/HeytingLean/Tests/MirandaDynamics/AllSanity.lean`

## 3) Roadmap (what to do next, in priority order)

### Phase A — Documentation truthfulness + navigation (high priority; low risk)

1. Update `WIP/miranda_integration.md`:
   - add a “Status (YYYY-MM-DD)” banner listing the actual Lean modules + executables,
   - clearly separate **Mechanized (Lean)** vs **Planned (external/literature)** sections,
   - link this plan + the research map note.
2. Ensure `WIP/Awaiting Paper Writing/subbooks_plan.md` references:
   - `WIP/miranda_integration.md`
   - `WIP/miranda_integration_plan.md`
   - and lists all Miranda demo executables.

### Phase B — External-results boundary refinement (medium priority; medium risk)

Goal: strengthen the “no axioms, but clear assumptions” story.

1. Split external interfaces into smaller, composable hypotheses:
   - a hypothesis for “a physical construction realizes a reaching relation”,
   - a hypothesis for “halting many-one reduces to predicate `P`”.
2. Add small theorems that consume only these interfaces to derive undecidability/non-computability.

Current status (implemented):
- Interfaces: `lean/HeytingLean/MirandaDynamics/External/Interfaces.lean`
  - `External.TKFTReachingFunctional` / `External.TKFTConstruction`
  - `External.HaltingToPredicate` / `External.HaltingReduction`
- Named wrappers: `lean/HeytingLean/MirandaDynamics/External/Claims.lean`
- Consequences: `lean/HeytingLean/MirandaDynamics/External/Consequences.lean` (e.g. `¬ComputablePred` transfers)

### Phase C — Unification theorem (hypothesis-first) (research track)

Goal: state a “Heyting–Turing correspondence” theorem *only* at the abstract nucleus/reachability level
already present in Lean, with explicit hypotheses (no PDE/billiard claims inside Lean).

Deliverable suggestion:
- `lean/HeytingLean/MirandaDynamics/HeytingTuring/Correspondence.lean` (new module)

### Phase D — Billiards analytic strengthening (research track)

Goal: mechanize additional Miranda–Ramos analytic lemmas that avoid billiard geometry, building on
`CantorEncoding.lean` and Mathlib’s Cantor-set infrastructure.

### Phase E — Full external formalization (long-horizon)

Goal: eventually mechanize the TKFT/billiards/Euler/Navier–Stokes constructions themselves (not just
their downstream consequences). This is a multi-quarter effort.

Backlog/decomposition:
- `WIP/miranda_full_formalization_backlog_2026-01-17.md`

## 4) QA protocol (must follow `AGENTS.md`)

### Dev Mode (default during implementation)

```bash
./scripts/qa_dev.sh --modules HeytingLean.MirandaDynamics
```

### Quick Mode (before commit/PR)

```bash
./scripts/guard_no_sorry.sh
(cd lean && lake build --wfail)
./scripts/build_all_exes.sh --strict
./scripts/run_all_exes.sh
./scripts/qa_robustness_all.sh
./scripts/qa_portability.sh
```

### Hostile-env spot checks (Miranda demos)

```bash
env -i PATH="" ./lean/.lake/build/bin/miranda_dynamics_demo
env -i PATH="" ./lean/.lake/build/bin/miranda_billiards_demo
env -i PATH="" ./lean/.lake/build/bin/miranda_billiards_geometry_demo
env -i PATH="" ./lean/.lake/build/bin/miranda_discrete_demo
env -i PATH="" ./lean/.lake/build/bin/miranda_partialflow_demo
```
