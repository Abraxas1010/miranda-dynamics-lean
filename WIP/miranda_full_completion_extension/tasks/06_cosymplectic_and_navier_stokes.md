# WS6 Tasks: Cosymplectic geometry & Navier–Stokes steady states (2026-01-17)

## Goal

Mechanize the cosymplectic-geometry objects and the Navier–Stokes steady-state universality reduction,
replacing the current external claim wrapper with actual Lean proofs.

This is a long-horizon workstream, but we break it into definition-first milestones that can be landed
independently (and tested) without committing to the full paper proof immediately.

## External references (primary)

- Dyhr, González-Prieto, Miranda, Peralta-Salas, “Turing complete Navier-Stokes steady states via cosymplectic geometry”.
  - arXiv:2507.07696: https://arxiv.org/abs/2507.07696
- Related cosymplectic/Reeb paper (for background definitions):
  - arXiv:2505.10379: https://arxiv.org/abs/2505.10379

## Inputs (existing assets to reuse)

### In this repo
- External claim wrapper (to eventually delete/retire):
  - `lean/HeytingLean/MirandaDynamics/External/Claims.lean`
  - `lean/HeytingLean/MirandaDynamics/External/Consequences.lean`
- Undecidability-transfer spine:
  - `lean/HeytingLean/MirandaDynamics/Undecidability/Transfers.lean`

### In Mathlib
- ODE/integral curves for flows (WS1)
- differential forms on normed spaces (WS2)

## What’s missing / “no turnkey solution”

No ready-to-reuse Lean cosymplectic-geometry library was identified in local scans or initial external searches.
Therefore, WS6 must start with:

1) precise definitions,  
2) minimal API lemmas,  
3) only then the universality construction.

## Task list (decomposed)

### WS6.1 Definition audit (Research-needed)

- [ ] Extract the paper’s definitions of cosymplectic structures used in the construction:
  - base manifold assumptions,
  - defining forms / nondegeneracy,
  - associated vector fields/flows.
- [ ] Decide a Lean-friendly representation aligned with WS2 (forms):
  - Euclidean-first vs manifold-level forms.

**Acceptance:** a “Lean definition sketch” for cosymplectic structure recorded in this file (not as axioms).

### WS6.2 Implement cosymplectic structure shell (Complex)

- [ ] Create `lean/HeytingLean/MirandaDynamics/Fluids/Cosymplectic.lean` (or `Geometry/Cosymplectic`):
  - structure definition,
  - basic lemmas (uniqueness of associated vector field under hypotheses, etc.).

**Acceptance:** compiles with `--wfail` and includes at least one nontrivial lemma.

### WS6.3 Bridge to (partial) flows and reaching relations (Complex)

- [ ] Use WS1 machinery to define reaching relations induced by the cosymplectic-associated flow(s).

**Acceptance:** a lemma connecting the flow to a reaching relation, plus a tiny demo or proof-level sanity check.

### WS6.4 Navier–Stokes steady state formalization (Very Complex)

- [ ] Decide a formalism for Navier–Stokes steady states in Lean:
  - likely requires significant PDE infrastructure not currently in Mathlib.
- [ ] If PDE layer is missing, define a staged plan:
  - first mechanize the geometric reduction “computation ↦ cosymplectic data ↦ dynamical predicate”,
    leaving the PDE verification as a separate later task.

**Acceptance:** a written decomposition into PDE prerequisites vs geometric steps, so work can proceed honestly.

### WS6.5 Replace external claim usage (Moderate, endgame)

- [ ] Once a mechanized reduction exists, remove or supersede the external `NavierStokesTuringCompleteClaim`.

## QA protocol (incremental)

- Dev: `./scripts/qa_dev.sh --modules HeytingLean.MirandaDynamics`

## Progress log

- 2026-01-17: (placeholder) Task file created; no code changes in this WS yet.

