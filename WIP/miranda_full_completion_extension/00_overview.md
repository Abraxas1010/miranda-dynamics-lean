# Project Extension: “Full Miranda/TKFT/Billiards/Fluids Formalization” (2026-01-17)

This folder restarts the planning+research process for pushing the Miranda/TKFT/billiards/Euler/Navier–Stokes
track from the current **Lean-realistic spine** to **fully mechanized** mathematics in Lean.

It is intentionally decomposed into *workstreams* with independently checkable milestones, so we can keep:
- `lake build --wfail` green (incremental, no `sorry`/`admit`),
- all `lean_exe` targets building and running,
- hostile-environment robustness tests passing,
- documentation honest (no “paper claims” asserted as Lean theorems).

## 0) Current baseline (already mechanized)

Before starting any “full completion” work, treat the current spine as the baseline contract:
- Status + file inventory: `WIP/miranda_integration.md`
- Lean-realistic scoped plan: `WIP/miranda_integration_plan.md`
- Evidence+mapping note (paper ↔ Lean): `WIP/miranda_research_map_2026-01-17.md`
- Long-horizon backlog (high-level): `WIP/miranda_full_formalization_backlog_2026-01-17.md`

## 1) What “fully complete” means here (Definition of Done)

“Fully complete” **does not** mean “the interface is stated.” It means:

1. Theorems currently packaged as external claims in
   `lean/HeytingLean/MirandaDynamics/External/*` have been replaced by *actual Lean proofs*
   (possibly under explicit, formal hypotheses like regularity/compactness assumptions).
2. The geometric/dynamical/PDE objects used in those proofs are **defined in Lean** and have enough API
   to support the Miranda/Peralta-Salas constructions.
3. The full repo continues to satisfy the QA contract:
   - Dev Mode during work: `./scripts/qa_dev.sh --modules HeytingLean.MirandaDynamics`
   - Executable-first: build+run affected `lean_exe` targets, plus robustness tests on affected exes.
4. Any new theorems land into the documentation story:
   - update `WIP/Awaiting Paper Writing/subbooks_plan.md` (assignment),
   - update `Blueprint/blueprint/src/content.tex` with `\\lean{...}` references when narrative exists,
     or place them into clearly marked future-work sections.

**Reality check:** this is a multi-quarter effort. This extension plan exists to keep progress honest and
modular, not to promise a short timeline.

## 2) Research-first process (mandatory)

For each workstream below:

1. **Internal search first**
   - `./scripts/search.sh` in `HeytingLean.MirandaDynamics.*` and adjacent Mathlib modules
   - semantic overlay / traces when proving is involved (`scripts/prove_assist.py`, etc.)
2. **External search second** (recorded in the research map file)
   - Mathlib documentation / existing Lean projects
   - nLab for definitions
   - other provers for prior art (Coq/Isabelle/Agda)
   - papers/texts for authoritative statements
3. **Only then implement**, with:
   - small, testable definitions first,
   - minimal executable(s) for runtime smoke tests,
   - incremental QA (no clean builds unless explicitly triggered by policy).

The consolidated evidence log is:
- `WIP/miranda_full_completion_extension/00_research_map_2026-01-17.md`

## 3) Workstreams (each has its own task file)

Order is by “unblockers first” and “reuse first”.

### WS1 — Smooth flows & reaching semantics
Goal: bridge Mathlib’s ODE/integral-curve machinery to a reusable “(partial) flow induces reaching relation”
API that later geometry can reuse.

- Tasks: `WIP/miranda_full_completion_extension/tasks/01_smooth_flows_and_reaching.md`

### WS2 — Differential forms on manifolds (or a pragmatic substitute)
Goal: define enough differential form machinery on manifolds (or a chart-local surrogate) to express contact
and cosymplectic structures used by the fluids papers.

- Tasks: `WIP/miranda_full_completion_extension/tasks/02_manifold_differential_forms.md`

### WS3 — Contact geometry layer (definition-first → API → minimal theorems)
Goal: contact form, Reeb vector field, basic uniqueness/existence (under hypotheses), and a bridge to the
ODE flow layer.

- Tasks: `WIP/miranda_full_completion_extension/tasks/03_contact_geometry.md`

### WS4 — Vector calculus / Beltrami layer (needed for Euler steady states)
Goal: a Lean formalization path for “Beltrami field ⇒ Euler steady solution”, likely via differential forms
and Hodge star rather than ad-hoc `curl`.

- Tasks: `WIP/miranda_full_completion_extension/tasks/04_vector_calculus_and_beltrami.md`

### WS5 — Euler universality construction
Goal: mechanize the Euler universality encoding and the reduction from halting to an Euler dynamical
predicate, eliminating the external claim wrapper.

- Tasks: `WIP/miranda_full_completion_extension/tasks/05_euler_universality.md`

### WS6 — Cosymplectic geometry & Navier–Stokes steady states
Goal: define cosymplectic structures and the key objects referenced in the Navier–Stokes steady-state
universality paper, then mechanize the reduction.

- Tasks: `WIP/miranda_full_completion_extension/tasks/06_cosymplectic_and_navier_stokes.md`

### WS7 — Billiard geometry (reflection law + trajectory semantics)
Goal: formal billiard tables, specular reflection, trajectory evolution, and the bridge to the already
mechanized Cantor encoding spine.

- Tasks: `WIP/miranda_full_completion_extension/tasks/07_billiards_geometry.md`

### WS8 — TKFT “clean dynamical bordisms” (structure + gluing)
Goal: define a Lean notion of the TKFT clean dynamical bordism and prove the compositional semantics
law (gluing ↔ relation composition).

- Tasks: `WIP/miranda_full_completion_extension/tasks/08_tkft_bordisms.md`

## 4) Suggested execution policy (to reduce human bias but keep reality checks)

- Default: I proceed workstream-by-workstream and only ask for input when there is a genuine fork:
  definition choices that affect downstream architecture, or a substantial refactor risk.
- Every milestone ends with:
  - `./scripts/qa_dev.sh --modules HeytingLean.MirandaDynamics`
  - build+run affected executables
  - robustness checks on affected executables
  - an updated short progress note at the bottom of the relevant WS task file.

