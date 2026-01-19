import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import HeytingLean.MirandaDynamics.Billiards.PaperMapGenShift

/-!
# MirandaDynamics.Billiards: Cantor blocks and affine pieces for `paperFgen?` (WS7.4)

The WS7.4 “paper map” `paperFgen?` is *piecewise affine* once the head index `k` and the current
digit `cur` are fixed.

This file:
* packages the corresponding “Cantor blocks” as subsets of `ℝ²`;
* constructs an explicit `AffineMap` for each block;
* proves `paperFgen?` agrees with that affine map on the block.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set

/-- A “Cantor block” for the generalized paper map: the head index is `k` (via `z ∈ headInterval k`)
and the relevant Cantor digit of `x` is the fixed boolean `cur`. -/
def CantorBlock (k : ℤ) (cur : Bool) : Set (ℝ × ℝ) :=
  { p | p.2 ∈ headInterval k ∧ cantorDigitAt? (indexNat k) p.1 = some cur }

/-! ## Affine representatives -/

/-- View `τ_k` as an affine map in the tape coordinate. -/
noncomputable def tauAffine (k : ℤ) : ℝ →ᵃ[ℝ] ℝ :=
  if _ : k < 0 then
    ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (headScale k)).toAffineMap +
      AffineMap.const (k := ℝ) (P1 := ℝ) (headScale k)
  else
    ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (headScale k)).toAffineMap +
      AffineMap.const (k := ℝ) (P1 := ℝ) (1 - 2 * headScale k)

theorem tauAffine_apply (k : ℤ) (x : ℝ) : tauAffine k x = tau k x := by
  by_cases hk : k < 0
  · simp [tauAffine, tau, hk]
    ring_nf
  · simp [tauAffine, tau, hk]
    ring_nf

/-- The affine map corresponding to the `paperFgen?` branch determined by `(k, cur)`. -/
noncomputable def paperFgenAffine (next : Bool → Bool × ℤ) (k : ℤ) (cur : Bool) :
    (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) :=
  let out := next cur
  let b := out.1
  let dh := out.2
  let c : ℝ := writeDelta k b cur
  let xAff : (ℝ × ℝ) →ᵃ[ℝ] ℝ :=
    (LinearMap.fst ℝ ℝ ℝ).toAffineMap + AffineMap.const (k := ℝ) (P1 := (ℝ × ℝ)) c
  xAff.prod ((tauAffine (k + dh)).comp xAff)

theorem paperFgenAffine_apply (next : Bool → Bool × ℤ) (k : ℤ) (cur : Bool) (p : ℝ × ℝ) :
    paperFgenAffine next k cur p =
      let out := next cur
      let b := out.1
      let dh := out.2
      let x' := p.1 + writeDelta k b cur
      (x', tau (k + dh) x') := by
  classical
  -- Unfold the affine packaging and reduce to `tauAffine_apply`.
  simp [paperFgenAffine, tauAffine_apply]

/-! ## `paperFgen?` agrees with its affine representative on each block -/

theorem paperFgen?_eq_some_paperFgenAffine_of_mem (next : Bool → Bool × ℤ) {k : ℤ} {cur : Bool}
    {p : ℝ × ℝ} (hp : p ∈ CantorBlock k cur) :
    paperFgen? next p = some (paperFgenAffine next k cur p) := by
  classical
  rcases hp with ⟨hz, hcur⟩
  have hk : headIndex? p.2 = some k :=
    headIndex?_eq_some_of_mem (z := p.2) (k := k) hz
  -- Evaluate the `Option` branches; `paperFgenAffine_apply` rewrites the RHS to the same normal form.
  simp [paperFgen?, hk, hcur, paperFgenAffine_apply]

end Billiards
end MirandaDynamics
end HeytingLean
