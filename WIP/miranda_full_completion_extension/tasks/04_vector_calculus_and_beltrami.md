# WS4 Tasks: Vector calculus / Beltrami fields (2026-01-17)

## Goal

Provide the mathematical infrastructure to express and prove (at least in a restricted setting):

- the Euler steady-state equations,
- the definition of Beltrami fields (`curl u = λ u`) in a coordinate-free way,
- the implication “Beltrami ⇒ Euler steady solution” under appropriate hypotheses.

This workstream is a prerequisite for mechanizing the Euler universality construction (WS5).

## External references (background)

- Arnold & Khesin, “Topological Methods in Hydrodynamics” (book landing page):
  https://link.springer.com/book/10.1007/978-1-4757-2135-4

## Inputs (existing assets to reuse)

### In Mathlib
- ODE/integral curves (WS1), for dynamical flows once we have vector fields
- differential forms on normed spaces (WS2), which can provide a path to `curl` via Hodge star

### Negative scan result (important)

Local Mathlib scan did not find a “ready-to-use curl/div/grad vector calculus” API suitable for Euler PDE work.
Therefore, the likely path is to define the needed operators via differential forms:

1. Use an inner product + orientation on ℝ³ to get a Hodge star `⋆`,
2. Define `curl` in terms of `d` and `⋆` (standard differential-form formulation),
3. Define Euler equations in terms of Lie derivative / forms where possible.

## Task list (decomposed)

### WS4.1 Internal search: Hodge star / orientation / volume-form APIs (Research-needed)

- [x] Search Mathlib for Hodge star or star-operator machinery:
  - `rg -n "Hodge|hodge|star operator|volumeForm|VolumeForm|Orientation" lean/.lake/packages/mathlib/Mathlib -S | head`
  - `python3 scripts/mathlib_search.py --moogle "Hodge star"`
- [x] Record the concrete Lean identifiers (or confirm absence).

**Acceptance:** a written “reuse map” for the exact types we will use to define `curl`.

Outcome (2026-01-17): no `Hodge` / `hodge` / `HodgeStar` / `hodgeStar` identifiers were found in this
Mathlib pin. A scan *did* locate orientation/volume-form infrastructure (e.g. `Orientation.volumeForm`
in `Mathlib/Analysis/InnerProductSpace/TwoDim.lean` and related orientation files), but not a general
Hodge-star operator on alternating forms. We therefore keep the current coordinate-staging approach
for `curl` until a compatible Hodge-star path is identified.

Note: `python3 scripts/mathlib_search.py --moogle "Hodge star"` currently reports a Moogle HTTP 308
redirect and returns no results; the `rg` scan remains the source of truth for this checkpoint.

### WS4.2 Define `curl` on ℝ³ (Complex)

Depending on WS4.1 outcome:

- If Mathlib has Hodge star for the setting we need:
  - [ ] define `curl` for smooth vector fields (or 1-forms) using `⋆ d` and the musical isomorphisms.
- If not:
  - [ ] implement the minimum Hodge star on ℝ³ (likely restricted to `Fin 3 → ℝ` with standard basis),
    sufficient to define `curl` and prove a small lemma suite.

**Acceptance:** a Lean definition `curl` and at least one lemma showing it matches a basic identity on a simple field.

### WS4.3 Define Beltrami field and Euler steady equation shell (Moderate → Complex)

- [x] Define `IsBeltrami (u) (λ)` and a minimal steady Euler shell (pressure).
- [x] Prove “Beltrami ⇒ Euler steady (Bernoulli/Lamb form)” for the staged shell.

**Acceptance:** a theorem statement with a proof for the restricted setting where the form calculus is available.

### WS4.4 Executable smoke test (Moderate)

- [ ] Add a tiny executable that evaluates the symbolic/structural definitions for a simple explicit vector field,
  printing checks (not numerical PDE solving).
- [ ] Ensure hostile-env robustness: `env -i PATH="" ...` should not crash.

**Acceptance:** binary builds/runs, robustness tests pass.

## QA protocol (incremental)

- Dev: `./scripts/qa_dev.sh --modules HeytingLean.MirandaDynamics`

## Progress log

- 2026-01-17:
  - Added a staged coordinate `curl` operator on `ℝ³ := Fin 3 → ℝ` using `fderiv`:
    - `lean/HeytingLean/MirandaDynamics/Fluids/VectorCalculus/Curl3.lean` (`R3.curl`, `R3.IsBeltrami`).
    - Test: `lean/HeytingLean/Tests/MirandaDynamics/CurlSanity.lean`.
  - Added `grad`/`div` and a steady Euler (Bernoulli/Lamb form) shell:
    - `lean/HeytingLean/MirandaDynamics/Fluids/VectorCalculus/GradDiv3.lean` (`R3.grad`, `R3.div`,
      `R3.IsEulerSteadyBernoulli`).
    - Test: `lean/HeytingLean/Tests/MirandaDynamics/GradDivSanity.lean`.
  - This avoids introducing a Hodge-star dependency while the Mathlib Hodge-star story remains unclear.

- 2026-01-17 (extension continuation):
  - Proved the staged implication “Beltrami ⇒ Euler steady (Bernoulli/Lamb form)”:
    - `HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3.eulerSteadyBernoulli_const_of_beltrami`
      in `lean/HeytingLean/MirandaDynamics/Fluids/VectorCalculus/GradDiv3.lean`.
    - Test: `lean/HeytingLean/Tests/MirandaDynamics/GradDivSanity.lean`.
