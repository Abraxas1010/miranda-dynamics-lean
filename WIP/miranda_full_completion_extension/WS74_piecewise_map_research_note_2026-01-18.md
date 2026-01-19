# WS7.4 Research Note (2026-01-18): Paper map `f=(f₁,f₂)` vs Lean implementation

## Sources (primary)

- Eva Miranda, Carlos Ramos, “Classical billiards can compute”, arXiv:2512.19156 (Dec 2025).
  - PDF: `https://arxiv.org/pdf/2512.19156`

## What the paper needs (as used in our Lean code)

The computational “spine” we want in Lean is:

- a Cantor-set tape encoding `t ↦ x_t ∈ [0,1]`,
- a head-position embedding `τ_k : [0,1] → I_k` into disjoint intervals,
- a **piecewise-affine** map on the encoded invariant set that performs one symbolic step
  (read digit at head, write new digit, update head).

In the paper:

- `x_t` is a Cantor/ternary encoding (digits in `{0,2}`), and `x_{t,k} = τ_k(x_t)` is the combined
  encoding of tape + head position.
- Appendix A defines explicit Cantor “blocks” `I_{ε₁…ε_{2k}s}` (fixed finite prefix, fixed next digit)
  and their images under `τ_k` (used to realize wall segments / affine maps on each block).

## Lean mapping (what we implemented and where)

### 1) Cantor encoding + head embedding (`τ_k`)

- `lean/HeytingLean/MirandaDynamics/Billiards/CantorEncoding.lean`
  - `encodeTape : (ℤ → Bool) → ℝ`
  - `tau : ℤ → ℝ → ℝ`
  - `encodeWithHead t k = tau k (encodeTape t)`
  - `headInterval k` and disjointness lemmas

### 2) Explicit affine tape-write law (paper “write offset”)

- `lean/HeytingLean/MirandaDynamics/Billiards/CantorTapeUpdate.lean`
  - `encodeTape_write_eq_add_pow`:
    overwriting `t k` changes `encodeTape t` by a single explicit geometric-series term.

### 3) Paper map fragments (WS7.4)

We now have three increasingly “explicit” versions of the WS7.4 map:

- `lean/HeytingLean/MirandaDynamics/Billiards/PaperMap.lean`
  - `paperWriteF?` (write+shift) still takes the current digit `cur` as a parameter.

- `lean/HeytingLean/MirandaDynamics/Billiards/PaperMapFull.lean`
  - `paperFfull?` removes `cur` by decoding `x` via classical choice on the image of `encodeTape`.
  - Correctness on encoded points: `paperFfull?_encode_pair`.

- `lean/HeytingLean/MirandaDynamics/Billiards/CantorDigits.lean`
  - `cantorHeadDigit?`, `cantorTail?`, `cantorDigitAt?`
  - proves `cantorDigitAt? n (encodeTape t) = some (digits t n)`, hence reads `t k` at `n = indexNat k`.

- `lean/HeytingLean/MirandaDynamics/Billiards/PaperMapPiecewise.lean`
  - `paperFpiece?` removes `cur` using the **explicit digit-reading** `cantorDigitAt?` (no classical tape decoder).
  - Correctness on encoded points: `paperFpiece?_encode_pair`, `paperFpiece?_affine_on_encode`.

### 4) Unifying WS7.4 with WS5+ generalized shifts

- `lean/HeytingLean/MirandaDynamics/Computation/GeneralizedShift.lean`
  - `GenShiftRule` / `GenShiftCfg` and `GenShiftRule.step`

- `lean/HeytingLean/MirandaDynamics/Billiards/PaperMapGenShift.lean`
  - defines `paperFgen?` parameterized by a local generalized-shift rule `Bool → Bool × ℤ`
  - proves the conjugacy-on-image statement:
    `paperFgen?_encodeCfg : paperFgen? next (encodeCfg c) = some (encodeCfg (GenShiftRule.step ⟨next⟩ c))`

This is the current “best mechanized” version of the paper map story: it states a clean symbolic
dynamics theorem without committing to the billiard-geometry realization.

## Gaps remaining (true paper-faithful completion)

1) **Cantor block geometry**: formalize the appendix blocks `I_{ε…}` as explicit intervals and show
   `cantorDigitAt?` is constant on each block (hence `paperFgen?` is affine on each block).
2) **Finite control / full machine step**: connect `next : Bool → Bool × ℤ` to an actual reversible
   machine state (or to the repo’s `HaltSys`/`DetSys` encodings), i.e. expand the symbolic alphabet
   beyond a single `Bool` cell update.
3) **Billiard realization**: prove that the *actual* billiard return map equals `paperFgen?` on the
   invariant set (this is the long-horizon geometry/mechanics part).

