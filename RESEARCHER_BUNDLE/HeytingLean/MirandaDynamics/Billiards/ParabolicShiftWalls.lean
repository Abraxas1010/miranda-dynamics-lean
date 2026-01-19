import HeytingLean.MirandaDynamics.Billiards.SpecularReflection
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# MirandaDynamics.Billiards: parabolic shift walls (WS7.3 core reflection algebra)

The paper’s head-shift gadget is implemented geometrically using *parabolic walls with a common
focus*. The key geometric fact is the parabola’s reflection property:

> a vertical incoming ray reflects through the focus.

This file formalizes the **algebraic core** of that statement in `ℝ²` using the explicit reflection
formula `reflect_apply`. It does not yet build the full shift corridor geometry (two parabolas +
straight segments) needed to realize the affine `tau` update; that remains a longer proof task.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open scoped RealInnerProductSpace

namespace Plane

abbrev x (p : V) : ℝ := p 0
abbrev y (p : V) : ℝ := p 1

def mk (x y : ℝ) : V :=
  fun i => if i = 0 then x else y

def eX : V := mk 1 0
def eY : V := mk 0 1

@[simp] theorem mk_x (x y : ℝ) : Plane.x (mk x y) = x := by simp [mk, Plane.x]
@[simp] theorem mk_y (x y : ℝ) : Plane.y (mk x y) = y := by simp [mk, Plane.y]

@[simp] theorem eX_x : Plane.x eX = 1 := by simp [eX, mk_x]
@[simp] theorem eX_y : Plane.y eX = 0 := by simp [eX, mk_y]
@[simp] theorem eY_x : Plane.x eY = 0 := by simp [eY, mk_x]
@[simp] theorem eY_y : Plane.y eY = 1 := by simp [eY, mk_y]

end Plane

open Plane

namespace Parabola

/-- Standard upward-opening parabola `y = x^2 / (4f)` with focus at `(0,f)`. -/
def set (f : ℝ) : Set V :=
  { p | y p = (x p) ^ 2 / (4 * f) }

/-- Focus point `(0,f)`. -/
def focus (f : ℝ) : V :=
  mk 0 f

/-- A vertical translate of the standard parabola, chosen so that the focus is `(0,f₀)`.

For `f ≠ 0`, the set `{ p | y p = x^2/(4f) + f₀ - f }` is the parabola with focus `(0,f₀)` and
directrix `y = f₀ - 2f` (same axis). -/
def setWithFocus (f₀ f : ℝ) : Set V :=
  { p | y p = (x p) ^ 2 / (4 * f) + (f₀ - f) }

/-- Focus point `(0,f₀)` for the translated family. -/
def focusWith (f₀ : ℝ) : V :=
  mk 0 f₀

/-- The vertical translation vector mapping `setWithFocus f₀ f` back to `set f`. -/
def shiftVec (f₀ f : ℝ) : V :=
  mk 0 (f₀ - f)

/-- A convenient normal vector field for the parabola `y = x^2/(4f)`:
the implicit equation is `4f*y - x^2 = 0`, with gradient `(-2x, 4f)`, so we use `(x, -2f)` as a
scaled normal. -/
def normal (f : ℝ) (p : V) : V :=
  mk (x p) (-2 * f)

theorem mem_setWithFocus_iff (f₀ f : ℝ) (p : V) :
    p ∈ setWithFocus f₀ f ↔ y p = (x p) ^ 2 / (4 * f) + (f₀ - f) := Iff.rfl

theorem mem_set_iff (f : ℝ) (p : V) : p ∈ set f ↔ y p = (x p) ^ 2 / (4 * f) := Iff.rfl

theorem sub_shiftVec_mem_set_iff (f₀ f : ℝ) (p : V) :
    p - shiftVec f₀ f ∈ set f ↔ p ∈ setWithFocus f₀ f := by
  -- Translate `y` by `-(f₀-f)`; `x` is unchanged.
  simp [set, setWithFocus, shiftVec, Plane.mk, Plane.x, Plane.y, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

theorem inner_normal_neg_eY (f : ℝ) (p : V) :
    inner ℝ (normal f p) (-eY) = 2 * f := by
  -- Expand dot product in coordinates.
  simp [normal, Plane.eY, Plane.eX, Plane.mk, Plane.x, Plane.y, EuclideanSpace.inner_eq_sum_mul, Fin.sum_univ_two]

theorem norm_normal_sq (f : ℝ) (p : V) :
    ((‖normal f p‖ : ℝ) ^ 2) = (x p) ^ 2 + 4 * f ^ 2 := by
  have hinner : ((‖normal f p‖ : ℝ) ^ 2) = inner ℝ (normal f p) (normal f p) := by
    simpa using (real_inner_self_eq_norm_sq (x := normal f p)).symm
  -- Compute the dot product explicitly.
  -- `(-2*f)^2 = 4*f^2`.
  simpa [normal, Plane.mk, Plane.x, Plane.y, EuclideanSpace.inner_eq_sum_mul, Fin.sum_univ_two, pow_two, mul_add,
    add_mul, mul_assoc, mul_left_comm, mul_comm] using hinner

/-- Reflection of a vertical *downward* incoming ray across the parabola’s tangent line points toward the focus. -/
theorem reflect_neg_eY_eq_smul_focus_sub (f : ℝ) (hf : f ≠ 0) {p : V} (hp : p ∈ set f) :
    reflect (normal f p) (-eY) =
      ((4 * f) / ((x p) ^ 2 + 4 * f ^ 2)) • (focus f - p) := by
  -- Use the explicit reflection formula and simplify coordinatewise.
  have hn0 : ((‖normal f p‖ : ℝ) ^ 2) ≠ 0 := by
    -- The second component of the normal is `-2f`, so it is nonzero when `f ≠ 0`.
    have : (4 * f ^ 2 : ℝ) ≠ 0 := by
      nlinarith [hf]
    -- `x^2 + 4f^2 ≠ 0`.
    have hnorm : ((‖normal f p‖ : ℝ) ^ 2) = (x p) ^ 2 + 4 * f ^ 2 := norm_normal_sq (f := f) (p := p)
    -- `x^2 ≥ 0` so sum is nonzero.
    have : (x p) ^ 2 + 4 * f ^ 2 ≠ 0 := by
      have hx : 0 ≤ (x p) ^ 2 := by nlinarith
      have hf' : 0 < 4 * f ^ 2 := by
        have : 0 < (f ^ 2 : ℝ) := by nlinarith [hf]
        nlinarith
      exact ne_of_gt (lt_of_lt_of_le hf' (by nlinarith [hx]))
    exact hnorm ▸ this
  have hinner : inner ℝ (normal f p) (-eY) = 2 * f := inner_normal_neg_eY (f := f) (p := p)
  have hnorm : ((‖normal f p‖ : ℝ) ^ 2) = (x p) ^ 2 + 4 * f ^ 2 := norm_normal_sq (f := f) (p := p)
  -- Rewrite `reflect` using `reflect_apply` and then show both coordinates match.
  ext i <;> fin_cases i
  · -- x-coordinate
    -- `focus f - p` has x-coordinate `-x p`.
    simp [reflect_apply, normal, Plane.eY, Plane.mk, Plane.x, Plane.y, focus, hinner, hnorm, hn0, hp, sub_eq_add_neg,
      div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm]
    ring_nf
  · -- y-coordinate
    -- Use `hp : y = x^2/(4f)` to rewrite `focus - p`.
    have hpy : y p = (x p) ^ 2 / (4 * f) := hp
    simp [reflect_apply, normal, Plane.eY, Plane.mk, Plane.x, Plane.y, focus, hinner, hnorm, hn0, hpy, sub_eq_add_neg,
      div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm]
    ring_nf

/-- Same reflection property for the vertically-translated family with focus `(0,f₀)`. -/
theorem reflect_neg_eY_eq_smul_focusWith_sub (f₀ f : ℝ) (hf : f ≠ 0) {p : V} (hp : p ∈ setWithFocus f₀ f) :
    reflect (normal f p) (-eY) =
      ((4 * f) / ((x p) ^ 2 + 4 * f ^ 2)) • (focusWith f₀ - p) := by
  -- Translate `p` back to the standard parabola and reuse `reflect_neg_eY_eq_smul_focus_sub`.
  let p' : V := p - shiftVec f₀ f
  have hp' : p' ∈ set f := by
    -- `p' ∈ set f ↔ p ∈ setWithFocus f₀ f`.
    have := (sub_shiftVec_mem_set_iff (f₀ := f₀) (f := f) (p := p)).2 hp
    simpa [p'] using this
  -- `x` is invariant under the vertical translation; so is the chosen normal field.
  have hx : x p' = x p := by
    simp [p', shiftVec, Plane.x, Plane.mk]
  have hnormal : normal f p' = normal f p := by
    simp [normal, p', hx, Plane.mk]
  -- Focus shift identity: `(0,f) - p' = (0,f₀) - p`.
  have hfocus : focus f - p' = focusWith f₀ - p := by
    simp [focus, focusWith, p', shiftVec, Plane.mk, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  -- Apply the base lemma at `p'` and rewrite.
  simpa [p', hx, hnormal, hfocus] using (reflect_neg_eY_eq_smul_focus_sub (f := f) hf (p := p') hp')

/-- The reverse direction: a ray aimed at the focus reflects to a vertical ray (axis-parallel). -/
theorem reflect_focus_sub_eq_smul_neg_eY (f : ℝ) (hf : f ≠ 0) {p : V} (hp : p ∈ set f) :
    reflect (normal f p) (focus f - p) =
      (((x p) ^ 2 + 4 * f ^ 2) / (4 * f)) • (-eY) := by
  -- Apply `reflect` to the forward property and use involutivity.
  have h :=
    reflect_neg_eY_eq_smul_focus_sub (f := f) hf (p := p) hp
  -- `reflect` is linear.
  have h' : reflect (normal f p) (reflect (normal f p) (-eY)) =
      ((4 * f) / ((x p) ^ 2 + 4 * f ^ 2)) • reflect (normal f p) (focus f - p) := by
    simpa [map_smulₛₗ, LinearIsometryEquiv.map_smul, LinearIsometryEquiv.map_sub] using congrArg (fun v => reflect (normal f p) v) h
  -- Simplify the LHS using `reflect_reflect`.
  have h'' : -eY =
      ((4 * f) / ((x p) ^ 2 + 4 * f ^ 2)) • reflect (normal f p) (focus f - p) := by
    simpa [reflect_reflect] using h'
  -- Solve for `reflect ... (focus - p)` by multiplying by the inverse scalar.
  have hc : ((4 * f) / ((x p) ^ 2 + 4 * f ^ 2)) ≠ 0 := by
    nlinarith [hf]
  -- `a • v = w` implies `v = (1/a) • w`.
  have : reflect (normal f p) (focus f - p) =
      (((4 * f) / ((x p) ^ 2 + 4 * f ^ 2))⁻¹) • (-eY) := by
    -- rewrite `h''` and cancel scalar.
    simpa [hc, smul_smul, inv_mul_cancel_left₀] using (eq_smul_iff_eq_inv_smul₀ hc).1 h''
  -- Normalize the scalar.
  -- `(4f / D)⁻¹ = D / (4f)`.
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using this

theorem reflect_focusWith_sub_eq_smul_neg_eY (f₀ f : ℝ) (hf : f ≠ 0) {p : V} (hp : p ∈ setWithFocus f₀ f) :
    reflect (normal f p) (focusWith f₀ - p) =
      (((x p) ^ 2 + 4 * f ^ 2) / (4 * f)) • (-eY) := by
  -- Translate and reuse the base lemma.
  let p' : V := p - shiftVec f₀ f
  have hp' : p' ∈ set f := by
    have := (sub_shiftVec_mem_set_iff (f₀ := f₀) (f := f) (p := p)).2 hp
    simpa [p'] using this
  have hx : x p' = x p := by
    simp [p', shiftVec, Plane.x, Plane.mk]
  have hnormal : normal f p' = normal f p := by
    simp [normal, p', hx, Plane.mk]
  have hfocus : focus f - p' = focusWith f₀ - p := by
    simp [focus, focusWith, p', shiftVec, Plane.mk, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  simpa [p', hx, hnormal, hfocus] using
    (reflect_focus_sub_eq_smul_neg_eY (f := f) hf (p := p') hp')

end Parabola

end Billiards
end MirandaDynamics
end HeytingLean
