import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import HeytingLean.MirandaDynamics.Billiards.PaperMapFiniteControl
import HeytingLean.MirandaDynamics.Billiards.CantorBlockExplicit

/-!
# MirandaDynamics.Billiards: explicit affine pieces for the finite-control paper map (WS7.4)

`PaperMapFiniteControl.lean` defines `paperFctrl?`, which realizes a controlled generalized-shift
step on encoded configurations.

This file packages its branch conditions as “control Cantor blocks” (fixing the head index `k`,
control state `q`, and current digit `cur`) and proves:

* on each such block, `paperFctrl?` agrees with an explicit `AffineMap`.

This is the closest fully mechanizable normal form needed by the billiards/Euler realizations:
each branch is genuinely affine on an explicit invariant block.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set

open HeytingLean.MirandaDynamics.Computation

/-! ## Affine representatives for the head-state encoding -/

/-- `inset x = (x+1)/3` as an affine map. -/
noncomputable def insetAffine : ℝ →ᵃ[ℝ] ℝ :=
  ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight ((3 : ℝ)⁻¹)).toAffineMap +
    AffineMap.const (k := ℝ) (P1 := ℝ) ((3 : ℝ)⁻¹)

theorem insetAffine_apply (x : ℝ) : insetAffine x = inset x := by
  simp [insetAffine, inset]
  ring_nf

/-- `tauState m k q` as an affine map in the tape coordinate. -/
noncomputable def tauStateAffine (m : ℕ) (k : ℤ) (q : Fin m) : ℝ →ᵃ[ℝ] ℝ :=
  let a : ℝ := headScale k * ((m : ℝ)⁻¹) * ((3 : ℝ)⁻¹)
  let b : ℝ := headLeft k + headScale k * ((m : ℝ)⁻¹) * ((q.1 : ℝ) + ((3 : ℝ)⁻¹))
  ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight a).toAffineMap + AffineMap.const (k := ℝ) (P1 := ℝ) b

theorem tauStateAffine_apply (m : ℕ) (k : ℤ) (q : Fin m) (x : ℝ) :
    tauStateAffine m k q x = tauState m k q x := by
  classical
  simp [tauStateAffine, tauState, inset, div_eq_mul_inv]
  ring_nf

/-! ## Control Cantor blocks (branch domains) -/

/-- A control Cantor block: head coordinate lies in the `(k,q)` subinterval and the `k`-digit is `cur`. -/
def CtrlCantorBlock (m : ℕ) (k : ℤ) (q : Fin m) (cur : Bool) : Set (ℝ × ℝ) :=
  { p | p.2 ∈ headStateInterval m k q ∧ cantorDigitAt? (indexNat k) p.1 = some cur }

/-- Explicit version using cylinder-unions for the digit constraint. -/
def CtrlCantorBlockExplicit (m : ℕ) (k : ℤ) (q : Fin m) (cur : Bool) : Set (ℝ × ℝ) :=
  { p | p.2 ∈ headStateInterval m k q ∧ p.1 ∈ cantorDigitBlock (indexNat k) cur }

theorem CtrlCantorBlockExplicit_subset_CtrlCantorBlock (m : ℕ) (k : ℤ) (q : Fin m) (cur : Bool) :
    CtrlCantorBlockExplicit m k q cur ⊆ CtrlCantorBlock m k q cur := by
  intro p hp
  refine ⟨hp.1, ?_⟩
  exact cantorDigitAt?_eq_some_of_mem_cantorDigitBlock (n := indexNat k) (cur := cur) (x := p.1) hp.2

/-! ## Affine piece for a fixed `(k,q,cur)` branch -/

/-- The affine map corresponding to the `paperFctrl?` branch determined by `(k,q,cur)`. -/
noncomputable def paperFctrlAffine {m : ℕ} (next : Fin m → Bool → Fin m × Bool × ℤ) (k : ℤ) (q : Fin m)
    (cur : Bool) : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) :=
  let out := next q cur
  let q' := out.1
  let b := out.2.1
  let dh := out.2.2
  let c : ℝ := writeDelta k b cur
  let xAff : (ℝ × ℝ) →ᵃ[ℝ] ℝ :=
    (LinearMap.fst ℝ ℝ ℝ).toAffineMap + AffineMap.const (k := ℝ) (P1 := (ℝ × ℝ)) c
  xAff.prod ((tauStateAffine m (k + dh) q').comp xAff)

theorem paperFctrlAffine_apply {m : ℕ} (next : Fin m → Bool → Fin m × Bool × ℤ) (k : ℤ) (q : Fin m)
    (cur : Bool) (p : ℝ × ℝ) :
    paperFctrlAffine next k q cur p =
      let out := next q cur
      let q' := out.1
      let b := out.2.1
      let dh := out.2.2
      let x' := p.1 + writeDelta k b cur
      (x', tauState m (k + dh) q' x') := by
  classical
  simp [paperFctrlAffine, tauStateAffine_apply]

/-! ## `paperFctrl?` agrees with its affine representative on each block -/

theorem paperFctrl?_eq_some_paperFctrlAffine_of_mem {m : ℕ} (hm : 0 < m)
    (next : Fin m → Bool → Fin m × Bool × ℤ) {k : ℤ} {q : Fin m} {cur : Bool} {p : ℝ × ℝ}
    (hp : p ∈ CtrlCantorBlock m k q cur) :
    paperFctrl? next p = some (paperFctrlAffine next k q cur p) := by
  classical
  rcases hp with ⟨hz, hcur⟩
  have hkq : headIndexState? m p.2 = some (k, q) :=
    headIndexState?_eq_some_of_mem (m := m) hm (z := p.2) (kq := (k, q)) hz
  simp [paperFctrl?, hkq, hcur, paperFctrlAffine_apply]

theorem paperFctrl?_eq_some_paperFctrlAffine_of_mem_explicit {m : ℕ} (hm : 0 < m)
    (next : Fin m → Bool → Fin m × Bool × ℤ) {k : ℤ} {q : Fin m} {cur : Bool} {p : ℝ × ℝ}
    (hp : p ∈ CtrlCantorBlockExplicit m k q cur) :
    paperFctrl? next p = some (paperFctrlAffine next k q cur p) := by
  apply paperFctrl?_eq_some_paperFctrlAffine_of_mem (m := m) hm (next := next)
  exact CtrlCantorBlockExplicit_subset_CtrlCantorBlock m k q cur hp

end Billiards
end MirandaDynamics
end HeytingLean
