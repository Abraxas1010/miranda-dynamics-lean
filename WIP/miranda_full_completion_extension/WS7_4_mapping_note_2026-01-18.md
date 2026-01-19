# WS7.4 Mapping Note (2026-01-18): Billiards paper ↔ Lean Cantor encoding spine

Goal: unblock WS7.4 (“connect billiard dynamics to the Cantor encoding spine”) by extracting the
paper’s *explicit* encoding maps and identifying what can be mechanized next in Lean without yet
proving the full geometric billiard-map realization.

Primary source:
- Eva Miranda, Daniel Ramos, “Classical billiards can compute” (arXiv:2512.19156, Dec 2025):
  - https://arxiv.org/abs/2512.19156
  - HTML mirror used for quick scanning: https://ar5iv.labs.arxiv.org/html/2512.19156

## A) What is already mechanized (Lean)

File: `lean/HeytingLean/MirandaDynamics/Billiards/CantorEncoding.lean`

- Tape encoding `encodeTape : (ℤ → Bool) → ℝ` landing in the ternary Cantor set.
- Head-position embedding `tau k : ℝ → ℝ` and `headInterval k : Set ℝ`.
- The “shift law” (paper Lemma 1):
  - `tau_shift_law` and derived `encodeWithHead_shift`.

Interpretation:
- For a tape `t` and head position `k`, the paper’s scalar encoding `x_{t,k}` is realized as
  `encodeWithHead t k := tau k (encodeTape t)`.

Additional WS7.4 staging work (this extension):
- `lean/HeytingLean/MirandaDynamics/Billiards/PaperMap.lean`:
  - packages the paper’s Lemma 1 head update as a partial piecewise-affine map
    `paperF? : (ℝ × ℝ) → Option (ℝ × ℝ)` (shift-only skeleton),
  - proves the conjugacy statement `paperF?_encode_pair` for `(encodeTape t, encodeWithHead t k)`.
- `lean/HeytingLean/MirandaDynamics/Billiards/CantorTapeUpdate.lean`:
  - proves `encodeTape_write`: overwriting a single tape cell changes `encodeTape` by an explicit
    one-term correction in `Cardinal.cantorFunctionAux`.

## B) What the paper introduces next (WS7.4-critical)

Around §3.2 (billiard map definition), the paper defines a billiard map
`f = (f₁, f₂)` on a subset `X ⊆ ℝ²` with piecewise formulas (equations (9) and (11) in the paper
notation). The high-level structure is:

1) The “tape coordinate” (Cantor-set coordinate) evolves by a piecewise-affine map `f₁` that depends
   on the local symbol under the head.
2) The “head coordinate” evolves by an affine scaling/translation map `f₂` that matches the already
   mechanized `tau_shift_law` behavior.

The paper then claims a conjugacy between:
- the discrete computation dynamics (a generalized shift / symbolic machine model), and
- the map `f` restricted to the Cantor-like invariant set inside `X`,
and later claims `f` is realized as the actual billiard collision map for a constructed table `Q`.

## C) Proposed Lean staging for WS7.4

### C.1 (Next mechanizable milestone): formalize the *map-level* conjugacy

Define a **pure map** `f : ℝ × ℝ → ℝ × ℝ` (or `V := ℝ × ℝ`), with:
- explicit piecewise formulas matching the paper’s `f₁` and `f₂`,
- a “Cantor block” invariant subset `Xinv ⊆ ℝ²` (product of Cantor set with head intervals),
- and prove: for encoded states `(encodeTape t, encodeWithHead t k)` the map `f` simulates one
  step of a chosen discrete machine model (initially: a simplified shift/write rule).

This does **not** require any billiard geometry; it yields a rigorous Lean “dynamics-level” bridge:
`discrete_step` ↔ `f_step`.

### C.2 (Hard, later milestone): prove `f` is realized by a billiard table

This would require a full polygonal billiard formalization:
- existence/uniqueness of next collision,
- explicit wall normals,
- proving the resulting collision map matches the piecewise affine `f`.

Our current billiards development (`.../Billiards/Geometry.lean`, `.../UnitSquareMap.lean`) is a
useful semantic scaffold, but it is not yet the paper’s billiard table `Q`.

## D) Immediate subtask decomposition (what has “no turnkey solution”)

1) Extract the exact `f₁` and `f₂` formulas (paper equations (9) and (11)) into a precise Lean spec.
2) Decide a minimal “machine semantics” to target for the first conjugacy proof:
   - start with the head-shift-only skeleton (already mechanized),
   - then add a single-cell write rule and prove its effect on `encodeTape` as a series update.
3) Build the Cantor-block infrastructure:
   - product Cantor set `cantorSet × cantorSet` (Mathlib has `cantorSet`),
   - “blocks” as finite-depth cylinder sets and corresponding affine maps.

## E) Notes / risks

- Updating the tape encoding under a write operation is not a simple global affine map; it is best
  handled via `tsum` linearity and a lemma for sequences differing at finitely many indices.
- The project should reuse existing Mathlib lemmas for absolutely summable geometric series; avoid
  reinventing convergence proofs.
