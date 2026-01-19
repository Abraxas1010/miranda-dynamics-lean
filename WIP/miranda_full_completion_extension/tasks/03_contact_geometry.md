# WS3 Tasks: Contact geometry layer (2026-01-17)

## Goal

Build a **contact-geometry API** adequate for the Miranda/Peralta-Salas Euler universality track:
- contact form `α`,
- Reeb vector field `R_α`,
- Reeb flow and its basic properties,
in a way that composes with WS1 (flows → reaching relations).

## External references (definitions)

- Etnyre notes (contact form, Reeb vector field, basic results):
  https://math.gatech.edu/~etnyre/preprints/LectureNotes.pdf

## Inputs (existing assets to reuse)

### In this repo
- `lean/HeytingLean/MirandaDynamics/Fluids/ContactLinear.lean`
  - a **linear** “contact-like” package + uniqueness lemma (`reeb_unique`)
  - can serve as the linearization target for early contact definitions

### In Mathlib
- ODE / integral curves (WS1 inputs)
- differential forms on normed spaces (WS2 inputs)

## What’s missing / “no turnkey solution”

No ready-to-reuse Mathlib contact-geometry library was found in local scans.
Therefore we must choose a staged approach:

1. **Euclidean contact geometry first** (ℝ³ or ℝ^{2n+1}), based on WS2 Option A, then
2. **Manifold generalization** later if/when WS2 Option B is implemented.

## Task list (decomposed)

### WS3.1 Define Euclidean contact forms (Research-needed → Moderate)

- [x] Decide representation (dependent on WS2 decision):
  - likely `E := Fin (2*n+1) → ℝ` with normed-space differential forms
- [ ] Define `IsContactForm (α : 1-form)` as the usual nondegeneracy condition
  (in 3D: `α ∧ dα` nowhere-vanishing; in higher dims: `α ∧ (dα)^n`).
- [ ] Prove basic lemmas: invariance under scaling by a nowhere-zero function (as needed).

**Acceptance:** can typecheck the definition and prove one nontrivial lemma without sorries.

### WS3.2 Define Reeb vector field and uniqueness (Moderate)

- [x] Define `IsReeb (α) (R)` as:
  - `α(R)=1`
  - `i_R dα = 0`
- [x] Prove **uniqueness** under an explicit nondegeneracy hypothesis, reusing the idea of
  `ContactLinear.nondeg_ker` as a local surrogate if needed.

**Acceptance:** a lemma `reeb_unique` at the differential-form level (not just linear data).

### WS3.3 Existence of Reeb vector field (Research-needed → Complex)

In general, existence is nontrivial; on ℝ^{2n+1} for standard contact forms it is explicit.

- [ ] Implement explicit Reeb for a canonical contact form (e.g. standard contact form on ℝ³ / ℝ^{2n+1}).
- [ ] Prove it satisfies the Reeb equations.

**Acceptance:** “standard contact form has a Reeb field” as a Lean theorem (explicit construction).

### WS3.4 Reeb flow as (partial) flow, then reaching relation (Complex)

- [ ] Use WS1 `PartialFlow` to build a reaching relation from the Reeb flow.
- [ ] Provide a demo executable:
  - prints a small sanity check of the flow on a simple explicit contact form.

**Acceptance:** new demo builds/runs and integrates with `qa_robustness_affected.sh`.

## QA protocol (incremental)

- Dev: `./scripts/qa_dev.sh --modules HeytingLean.MirandaDynamics`

## Progress log

- 2026-01-17:
  - Added a small “Reeb flow” bridge for the existing linear contact-data spine:
    - `lean/HeytingLean/MirandaDynamics/Fluids/ContactLinearFlow.lean` (global translation flow `x ↦ x + t • R`).
    - Updated test `lean/HeytingLean/Tests/MirandaDynamics/FluidsSanity.lean` to exercise `reebFlow`.
  - Contact geometry proper (forms/manifolds) remains a future milestone in this WS.
- 2026-01-17:
  - Implemented Euclidean pointwise “contact/Reeb” predicates and Reeb uniqueness:
    - `lean/HeytingLean/MirandaDynamics/Geometry/Contact/Euclidean.lean` (`NondegKer`, `IsReebAt`,
      `reeb_unique_of_nondegKer`).
    - Test: `lean/HeytingLean/Tests/MirandaDynamics/ContactEuclideanSanity.lean`.
