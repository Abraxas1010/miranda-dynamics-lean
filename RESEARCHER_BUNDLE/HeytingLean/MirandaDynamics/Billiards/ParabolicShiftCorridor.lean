import HeytingLean.MirandaDynamics.Billiards.ParabolicShiftWalls
import HeytingLean.MirandaDynamics.Billiards.CantorEncoding

/-!
# MirandaDynamics.Billiards: two-parabola shift corridor (WS7.3 mechanizable core)

This file builds the next mechanizable layer on top of `ParabolicShiftWalls.lean`:

* define a horizontally-translated family of parabolas sharing a common focus;
* show that a two-bounce “parabola → parabola” corridor induces an **affine map** on the
  horizontal coordinate:

  `x ↦ a + (f₂/f₁) * (x - a)`.

Specializing to `(a,f₁,f₂) = (1,3,1)` yields the paper’s nonnegative-branch head shift
`z ↦ z/3 + 2/3`. The negative-branch map `z ↦ 3z` is the inverse affine map about `a=0`.

This does **not** yet assemble the full billiard table (corridors + straight connectors) nor the
minimal-time global `next?`. It isolates the hardest geometric “optics” nucleus needed for WS7.3.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open scoped RealInnerProductSpace

open Plane

namespace Parabola

/-! ## Horizontal translation (keep the same focus, shift the axis) -/

/-- Horizontal translation vector `(a,0)`. -/
def xShiftVec (a : ℝ) : V :=
  mk a 0

@[simp] theorem xShiftVec_x (a : ℝ) : x (xShiftVec a) = a := by
  simp [xShiftVec, Plane.mk, Plane.x]

@[simp] theorem xShiftVec_y (a : ℝ) : y (xShiftVec a) = 0 := by
  simp [xShiftVec, Plane.mk, Plane.y]

@[simp] theorem x_sub_xShiftVec (p : V) (a : ℝ) : x (p - xShiftVec a) = x p - a := by
  simp [xShiftVec, Plane.x, Plane.mk, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

@[simp] theorem y_sub_xShiftVec (p : V) (a : ℝ) : y (p - xShiftVec a) = y p := by
  simp [xShiftVec, Plane.y, Plane.mk, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

/-- Horizontally translated parabola family sharing focus `(a,f₀)`. -/
def setWithFocusX (a f₀ f : ℝ) : Set V :=
  { p | y p = (x p - a) ^ 2 / (4 * f) + (f₀ - f) }

/-- Focus point `(a,f₀)` for `setWithFocusX`. -/
def focusWithX (a f₀ : ℝ) : V :=
  mk a f₀

/-- Normal field for `setWithFocusX`: the same formula in the translated coordinate `x-a`. -/
def normalX (a f : ℝ) (p : V) : V :=
  mk (x p - a) (-2 * f)

theorem mem_setWithFocusX_iff (a f₀ f : ℝ) (p : V) :
    p ∈ setWithFocusX a f₀ f ↔ y p = (x p - a) ^ 2 / (4 * f) + (f₀ - f) := Iff.rfl

theorem sub_xShiftVec_mem_setWithFocus_iff (a f₀ f : ℝ) (p : V) :
    p - xShiftVec a ∈ setWithFocus f₀ f ↔ p ∈ setWithFocusX a f₀ f := by
  -- `setWithFocus` uses `y = x^2/(4f) + (f₀-f)`. After translating by `(a,0)`, `x ↦ x-a`.
  simp [setWithFocus, setWithFocusX, xShiftVec, Plane.x, Plane.y, Plane.mk, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm]

theorem normalX_eq_normal_sub_xShiftVec (a f : ℝ) (p : V) :
    normalX a f p = normal f (p - xShiftVec a) := by
  simp [normalX, normal, x_sub_xShiftVec, Plane.mk, Plane.x, Plane.y, xShiftVec]

theorem focusWithX_sub_eq_focusWith_sub (a f₀ : ℝ) (p : V) :
    focusWithX a f₀ - p = focusWith f₀ - (p - xShiftVec a) := by
  simp [focusWithX, focusWith, xShiftVec, Plane.mk, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-! ## Reflection property for translated parabolas -/

theorem reflect_neg_eY_eq_smul_focusWithX_sub (a f₀ f : ℝ) (hf : f ≠ 0) {p : V}
    (hp : p ∈ setWithFocusX a f₀ f) :
    reflect (normalX a f p) (-eY) =
      ((4 * f) / ((x p - a) ^ 2 + 4 * f ^ 2)) • (focusWithX a f₀ - p) := by
  -- Reduce to the vertical-translate lemma by shifting `x`.
  let p' : V := p - xShiftVec a
  have hp' : p' ∈ setWithFocus f₀ f := by
    have := (sub_xShiftVec_mem_setWithFocus_iff (a := a) (f₀ := f₀) (f := f) (p := p)).2 hp
    simpa [p'] using this
  have hx : x p' = x p - a := by simp [p']
  have hnormal : normal f p' = normalX a f p := by
    simpa [p', hx] using (normalX_eq_normal_sub_xShiftVec (a := a) (f := f) (p := p)).symm
  have hfocus : focusWith f₀ - p' = focusWithX a f₀ - p := by
    simpa [p'] using (focusWithX_sub_eq_focusWith_sub (a := a) (f₀ := f₀) (p := p)).symm
  -- Apply the existing lemma and rewrite.
  simpa [p', hx, hnormal, hfocus] using
    (reflect_neg_eY_eq_smul_focusWith_sub (f₀ := f₀) (f := f) hf (p := p') hp')

theorem reflect_focusWithX_sub_eq_smul_neg_eY (a f₀ f : ℝ) (hf : f ≠ 0) {p : V}
    (hp : p ∈ setWithFocusX a f₀ f) :
    reflect (normalX a f p) (focusWithX a f₀ - p) =
      (((x p - a) ^ 2 + 4 * f ^ 2) / (4 * f)) • (-eY) := by
  let p' : V := p - xShiftVec a
  have hp' : p' ∈ setWithFocus f₀ f := by
    have := (sub_xShiftVec_mem_setWithFocus_iff (a := a) (f₀ := f₀) (f := f) (p := p)).2 hp
    simpa [p'] using this
  have hx : x p' = x p - a := by simp [p']
  have hnormal : normal f p' = normalX a f p := by
    simpa [p', hx] using (normalX_eq_normal_sub_xShiftVec (a := a) (f := f) (p := p)).symm
  have hfocus : focusWith f₀ - p' = focusWithX a f₀ - p := by
    simpa [p'] using (focusWithX_sub_eq_focusWith_sub (a := a) (f₀ := f₀) (p := p)).symm
  simpa [p', hx, hnormal, hfocus] using
    (reflect_focusWith_sub_eq_smul_neg_eY (f₀ := f₀) (f := f) hf (p := p') hp')

/-! ## Two-parabola affine update -/

/-- Canonical point on `setWithFocusX a f₀ f` at horizontal coordinate `x0`. -/
def pointOn (a f₀ f x0 : ℝ) : V :=
  mk x0 ((x0 - a) ^ 2 / (4 * f) + (f₀ - f))

theorem pointOn_mem_setWithFocusX (a f₀ f x0 : ℝ) :
    pointOn a f₀ f x0 ∈ setWithFocusX a f₀ f := by
  simp [pointOn, setWithFocusX, Plane.mk, Plane.x, Plane.y]

/-- The affine map on `x` induced by the two-parabola corridor. -/
noncomputable def affineUpdate (a f₁ f₂ : ℝ) (x0 : ℝ) : ℝ :=
  a + (f₂ / f₁) * (x0 - a)

/-- The inverse affine map about the same fixed point `a`. -/
noncomputable def affineUpdateInv (a f₁ f₂ : ℝ) (x0 : ℝ) : ℝ :=
  a + (f₁ / f₂) * (x0 - a)

/-- The “inner hit” point obtained by moving from the common focus toward `pointOn … f₁ …`. -/
def innerHit (a f₀ f₁ f₂ x0 : ℝ) : V :=
  focusWithX a f₀ + (f₂ / f₁) • (pointOn a f₀ f₁ x0 - focusWithX a f₀)

@[simp] theorem x_innerHit (a f₀ f₁ f₂ x0 : ℝ) :
    x (innerHit a f₀ f₁ f₂ x0) = affineUpdate a f₁ f₂ x0 := by
  simp [innerHit, affineUpdate, Plane.x, Plane.mk, focusWithX, pointOn, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm, mul_assoc, mul_left_comm, mul_comm]
  ring_nf

theorem innerHit_eq_pointOn (a f₀ f₁ f₂ x0 : ℝ) (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0) :
    innerHit a f₀ f₁ f₂ x0 = pointOn a f₀ f₂ (affineUpdate a f₁ f₂ x0) := by
  -- Compare coordinates. The `x`-coordinate is the affine update; the `y`-coordinate follows by algebra.
  ext i <;> fin_cases i
  · simpa [x_innerHit] using (x_innerHit (a := a) (f₀ := f₀) (f₁ := f₁) (f₂ := f₂) (x0 := x0))
  · -- `y`-coordinate computation.
    have hy1 : y (innerHit a f₀ f₁ f₂ x0) =
        f₀ + (f₂ / f₁) * ((x0 - a) ^ 2 / (4 * f₁) - f₁) := by
      -- Expand the affine combination `focus + r • (p1 - focus)`.
      simp [innerHit, focusWithX, pointOn, Plane.y, Plane.mk, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        mul_assoc, mul_left_comm, mul_comm, smul_add, add_smul]
      ring_nf
    have hx2 : affineUpdate a f₁ f₂ x0 - a = (f₂ / f₁) * (x0 - a) := by
      simp [affineUpdate]
      ring_nf
    have hy2 :
        f₀ + (f₂ / f₁) * ((x0 - a) ^ 2 / (4 * f₁) - f₁) =
          (affineUpdate a f₁ f₂ x0 - a) ^ 2 / (4 * f₂) + (f₀ - f₂) := by
      -- Algebra; `hf₁` and `hf₂` are used only to clear denominators.
      field_simp [hf₁, hf₂, hx2]
      ring_nf
    -- Finish by rewriting the RHS into the `pointOn` formula.
    simpa [pointOn, Plane.y, Plane.mk, hy1] using hy2

theorem innerHit_mem_setWithFocusX (a f₀ f₁ f₂ x0 : ℝ) (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0) :
    innerHit a f₀ f₁ f₂ x0 ∈ setWithFocusX a f₀ f₂ := by
  -- Rewrite via `innerHit_eq_pointOn`.
  have hEq :=
    innerHit_eq_pointOn (a := a) (f₀ := f₀) (f₁ := f₁) (f₂ := f₂) (x0 := x0) hf₁ hf₂
  -- `pointOn` is on the parabola by definition.
  simpa [hEq] using (pointOn_mem_setWithFocusX (a := a) (f₀ := f₀) (f := f₂) (x0 := affineUpdate a f₁ f₂ x0))

/-! ## Specialization to the paper head shift law -/

theorem affineUpdate_one_three_one (z : ℝ) : affineUpdate 1 3 1 z = z / 3 + 2 / 3 := by
  simp [affineUpdate, div_eq_mul_inv]
  ring_nf

theorem affineUpdateInv_zero_three_one (z : ℝ) : affineUpdateInv 0 3 1 z = 3 * z := by
  simp [affineUpdateInv, div_eq_mul_inv]
  ring_nf

theorem headShift_eq_affineUpdate (k : ℤ) (z : ℝ) :
    headShift k z = if k < 0 then affineUpdateInv 0 3 1 z else affineUpdate 1 3 1 z := by
  by_cases hk : k < 0
  · simp [headShift, hk, affineUpdateInv_zero_three_one]
  · simp [headShift, hk, affineUpdate_one_three_one]

end Parabola

/-! ## A deterministic “shift corridor” cross-section map (non-global, WS7.3 building block) -/

namespace ParabolicShiftCorridor

open Parabola

/-- Cross-section state for the shift gadget: a head-coordinate `z` tagged with its head index `k`. -/
structure CollisionState where
  k : ℤ
  z : ℝ
  hz : z ∈ headInterval k

/-- “Good” shift states exclude the singular boundary; here we keep it as a hypothesis-style predicate. -/
def Good (_s : CollisionState) : Prop := True

/-- One-step shift update on the head coordinate (paper Lemma 1), expressed as the two-parabola affine form. -/
noncomputable def nextCoord (k : ℤ) (z : ℝ) : ℝ :=
  if k < 0 then Parabola.affineUpdateInv 0 3 1 z else Parabola.affineUpdate 1 3 1 z

theorem nextCoord_eq_headShift (k : ℤ) (z : ℝ) : nextCoord k z = headShift k z := by
  classical
  by_cases hk : k < 0
  · simp [nextCoord, headShift, hk, Parabola.affineUpdateInv_zero_three_one]
  · simp [nextCoord, headShift, hk, Parabola.affineUpdate_one_three_one]

/-- Deterministic next step for the shift corridor on the head coordinate. -/
noncomputable def next? (s : CollisionState) : Option CollisionState :=
  some
    { k := s.k + 1
      z := nextCoord s.k s.z
      hz := by
        -- `nextCoord` matches `headShift`, and `headShift` maps head intervals to the successor interval.
        simpa [nextCoord_eq_headShift] using headShift_mem_headInterval_succ s.k s.hz }

theorem next?_eq_some (s : CollisionState) : ∃ s', next? s = some s' := by
  refine ⟨{ k := s.k + 1, z := nextCoord s.k s.z, hz := ?_ }, ?_⟩
  · simpa [nextCoord_eq_headShift] using headShift_mem_headInterval_succ s.k s.hz
  · simp [next?]

theorem semiconj_headShift (s : CollisionState) :
    Option.map (fun s' => s'.z) (next? s) = some (headShift s.k s.z) := by
  simp [next?, nextCoord_eq_headShift]

theorem nextCoord_tau (k : ℤ) (x : ℝ) :
    nextCoord k (tau k x) = tau (k + 1) x := by
  -- Transport through the already-proved shift law.
  simp [nextCoord_eq_headShift, headShift_tau]

end ParabolicShiftCorridor

end Billiards
end MirandaDynamics
end HeytingLean
