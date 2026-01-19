# WS7.4 Extension Note (2026-01-18): Cantor Blocks + Finite Control in the Head Coordinate

## Goal
Mechanize the “piecewise-affine” structure of the paper-level map by:
1) packaging the branch conditions as **Cantor blocks**, and
2) extending the encoding to carry **finite control state** (a machine state) in the head coordinate.

This supports the next long-horizon steps (billiards / Euler realizations) by giving a clean symbolic
dynamics target: a controlled generalized shift whose one-step map is realized by an explicit partial
map on `ℝ²`.

## Primary external reference (paper)
- Miranda–Ramos, *Classical billiards can compute*, arXiv:2512.19156 (Dec 2025).
  - We use only the paper-level idea “fix a digit branch ⇒ affine update”; the full billiard geometry
    is not formalized here.

## Lean mapping (new mechanized modules)

### Cantor blocks (piecewise affine on fixed `(k,cur)`)
- `lean/HeytingLean/MirandaDynamics/Billiards/CantorBlocks.lean`
  - `HeytingLean.MirandaDynamics.Billiards.CantorBlock`
  - `HeytingLean.MirandaDynamics.Billiards.paperFgenAffine`
  - `HeytingLean.MirandaDynamics.Billiards.paperFgen?_eq_some_paperFgenAffine_of_mem`

**Interpretation:** on the block where the head index is `k` and the `k`-th Cantor digit is `cur`,
`paperFgen?` agrees with a single `AffineMap` (so the branch is genuinely affine).

### Explicit cylinders (paper-style finite prefixes)
- `lean/HeytingLean/MirandaDynamics/Billiards/CantorCylinders.lean`
  - `HeytingLean.MirandaDynamics.Billiards.cantorCylinder` (recursive, explicit)
  - `HeytingLean.MirandaDynamics.Billiards.cantorDigitAt?_eq_get?_of_mem_cantorCylinder`
  - `HeytingLean.MirandaDynamics.Billiards.cantorDigitBlock` (union of cylinders for an `n`-th digit)
  - `HeytingLean.MirandaDynamics.Billiards.cantorDigitAt?_eq_some_of_mem_cantorDigitBlock`

- `lean/HeytingLean/MirandaDynamics/Billiards/CantorBlockExplicit.lean`
  - `HeytingLean.MirandaDynamics.Billiards.CantorBlockExplicit`
  - `HeytingLean.MirandaDynamics.Billiards.paperFgen?_eq_some_paperFgenAffine_of_mem_explicit`

**Interpretation:** this upgrades “blocks defined by the digit reader predicate” to a *paper-style*
description using explicit cylinder sets (finite ternary prefixes). This is the form expected by a
billiard return-map proof: each branch corresponds to an explicit affine preimage chain.

### Finite control (state carried in the head coordinate)
- `lean/HeytingLean/MirandaDynamics/Computation/GeneralizedShiftControl.lean`
  - `HeytingLean.MirandaDynamics.Computation.GenShiftCtrlRule`
  - `HeytingLean.MirandaDynamics.Computation.GenShiftCtrlCfg`
  - `HeytingLean.MirandaDynamics.Computation.GenShiftCtrlRule.step`

- `lean/HeytingLean/MirandaDynamics/Billiards/HeadStateEncoding.lean`
  - `HeytingLean.MirandaDynamics.Billiards.headStateInterval` (open subintervals)
  - `HeytingLean.MirandaDynamics.Billiards.tauState` / `encodeWithHeadState`
  - `HeytingLean.MirandaDynamics.Billiards.headIndexState?` (partial decoder)
  - `HeytingLean.MirandaDynamics.Billiards.headIndexState?_encodeWithHeadState`

- `lean/HeytingLean/MirandaDynamics/Billiards/PaperMapFiniteControl.lean`
  - `HeytingLean.MirandaDynamics.Billiards.paperFctrl?`
  - `HeytingLean.MirandaDynamics.Billiards.paperFctrl?_encodeCfgCtrl`

**Design note:** the state decoder is intentionally partial on boundaries (returns `none`), consistent
with the project’s “good phase space avoids boundaries” strategy. The encoder uses an “inset”
embedding `(x+1)/3` so encoded points land strictly inside each state subinterval.

## Reuse plan (next steps)
1) Upgrade from abstract “blocks defined by decoder preimages” to paper-style explicit cylinder sets
   (prefix intervals in ternary) when needed for billiard geometry statements.
2) Use `paperFctrl?_encodeCfgCtrl` as the symbolic target for a billiard return-map (WS7.4 → WS7.3).
3) Extend controlled shifts to the project’s halting/periodicity bridges (WS5+), by adding a
   simulation relation from the existing `HaltSys` model to `GenShiftCtrlCfg`.
