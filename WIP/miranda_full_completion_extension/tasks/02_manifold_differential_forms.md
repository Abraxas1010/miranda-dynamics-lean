# WS2 Tasks: Differential forms on manifolds (or a pragmatic substitute) (2026-01-17)

## Goal

Enable contact/cosymplectic geometry formalization by providing a way to express:
- 1-forms `α`,
- their exterior derivative `dα`,
- wedge products and volume forms,
on the spaces where the Miranda/Peralta-Salas constructions live (typically 3-manifolds).

## Inputs (existing assets to reuse)

### In Mathlib
- Differential forms on **normed spaces** + exterior derivative:
  - `Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
  - Docs: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/DifferentialForm/Basic.html

- Smooth manifolds + tangent bundles + vector fields:
  - `Mathlib/Geometry/Manifold/*`
  - integral curves exist/unique (feeds into WS1):
    https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/IntegralCurve/ExistUnique.html

## What’s missing / “no turnkey solution”

Local scan did not show an out-of-the-box “differential forms on manifolds” library comparable to the normed-space
form library. That implies we need a deliberate choice:

### Option A (pragmatic): Euclidean-first forms
Do early contact/cosymplectic work on `ℝ^n` / finite-dimensional inner product spaces using the existing
normed-space form API, then generalize later.

### Option B (ambitious): charted-manifold forms wrapper
Define a manifold `k`-form as a chart-local differential form with compatibility under transition maps.
This is the “right” abstraction but has a big API surface and will be slow.

This WS exists to decide and implement a minimum viable path.

## Task list (decomposed)

### WS2.1 Internal search: confirm status of manifold-form machinery (Research-needed)

- [x] Search Mathlib for any existing manifold differential-form definitions:
  - `rg -n "DifferentialForm.*Manifold|Manifold.*DifferentialForm|ExteriorDerivative.*Manifold" lean/.lake/packages/mathlib/Mathlib -S`
  - `python3 scripts/mathlib_search.py --moogle "differential form on a manifold"`
- [ ] If found: summarize the API and decide whether to adopt or wrap it.
- [x] If not found: record a short “gap analysis” here (what we need vs what exists).

**Acceptance:** written decision and rationale (Option A vs B).

Outcome (2026-01-17): we did not find a turnkey manifold differential-form library in this repo’s Mathlib checkout.
Mathlib explicitly notes in `Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean` that “same for manifolds” is
“not defined yet”. We therefore proceed with **Option A (Euclidean-first)** as the initial foundation layer.

### WS2.2 (If Option A) Euclidean-first foundation (Moderate)

- [x] Create `lean/HeytingLean/MirandaDynamics/Geometry/Forms/Euclidean.lean`:
  - choose a concrete model:
    - `E := (Fin n → ℝ)` with existing normed-space structure
  - define notations/helpers for 1-forms and 2-forms
  - wrappers for `d` (exterior derivative) with simp lemmas

**Acceptance:** a small lemma about `d (d ω) = 0` compiles and passes `--wfail`.

Status (2026-01-17): implemented a small wrapper around Mathlib’s `extDeriv` as `Forms.d`, and re-exported
`d ∘ d = 0` as `Forms.d_d_eq_zero` in `lean/HeytingLean/MirandaDynamics/Geometry/Forms/Euclidean.lean`.
Added a proof-level smoke test `lean/HeytingLean/Tests/MirandaDynamics/FormsSanity.lean`.

### WS2.3 (If Option B) Manifold-form definition skeleton (Complex)

- [ ] Add `lean/HeytingLean/MirandaDynamics/Geometry/Forms/Manifold.lean` with:
  - a *minimal* structure for “manifold k-forms” sufficient to state contact/cosymplectic definitions
  - explicit TODO list of missing lemmas (kept as *tasks*, not `sorry`)
- [ ] Prove at least:
  - pullback compatibility under smooth maps (for chart transitions)
  - definition of `d` compatible with charted representation (may require substantial work)

**Acceptance:** ability to state “contact form” on a manifold without axioms/sorries.

Pragmatic intermediate milestone (2026-01-17): added a *chart-local surrogate* file
`lean/HeytingLean/MirandaDynamics/Geometry/Forms/Manifold.lean` that wraps Mathlib’s
`extDerivWithin` as `Forms.dWithin`, together with `dWithin ∘ dWithin = 0` lemmas
(`Forms.dWithin_dWithin_eqOn` / `Forms.dWithin_dWithin_eq_zero`).

This does **not** yet provide a true manifold exterior derivative, but it is useful for:
- open-subset-of-`ℝⁿ` staging,
- chart-local reasoning once a chart/transition API is selected.

### WS2.4 Hodge star / volume form prerequisites (Research-needed → Complex)

Beltrami/Euler work (WS4/WS5) often needs:
- metric,
- orientation,
- Hodge star,
to define `curl` in a coordinate-free way (via 1-forms/2-forms).

- [ ] Search Mathlib for Hodge star / orientation APIs:
  - `rg -n "Hodge|hodge|star operator|volume form|Orientation" lean/.lake/packages/mathlib/Mathlib -S | head`
  - `python3 scripts/mathlib_search.py --moogle "Hodge star"`
- [ ] If available: map the types we need (1-forms ↔ 2-forms) and record it.
- [ ] If not available: add a subtask list for building the minimal Hodge machinery required for ℝ³.

**Acceptance:** a concrete plan for defining `curl` (even if implementation is deferred to WS4).

Status (2026-01-17): a local scan finds extensive `Orientation` / `volumeForm` infrastructure for finite-dimensional
inner product spaces, but no apparent `HodgeStar`/`hodgeStar` operator API. This suggests we will need to define a
minimal Hodge-star layer ourselves for the restricted Euclidean setting (likely ℝ³), then use it to define `curl`
via differential forms in WS4.

## QA protocol (incremental)

- Dev: `./scripts/qa_dev.sh --modules HeytingLean.MirandaDynamics`

## Progress log

- 2026-01-17:
  - Chose Option A (Euclidean-first) based on Mathlib’s current “manifolds not defined yet” note.
  - Implemented `lean/HeytingLean/MirandaDynamics/Geometry/Forms/Euclidean.lean` and test
    `lean/HeytingLean/Tests/MirandaDynamics/FormsSanity.lean`.
  - Added `lean/HeytingLean/MirandaDynamics/Geometry/Forms/Manifold.lean` (set-within exterior derivative wrapper),
    and extended `lean/HeytingLean/Tests/MirandaDynamics/FormsSanity.lean` with a `dWithin∘dWithin=0` smoke test.
