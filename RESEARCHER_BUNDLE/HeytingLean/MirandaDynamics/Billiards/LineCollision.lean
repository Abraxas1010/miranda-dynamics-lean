import HeytingLean.MirandaDynamics.Billiards.SpecularReflection
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# MirandaDynamics.Billiards: line collision algebra (WS7 geometry support)

This file provides small, reusable lemmas for intersecting a ray `p + t • v` with an affine line
given by a normal `n` and an offset `c`:

  `Line n c := { q | ⟪n,q⟫ = c }`.

This is a prerequisite for mechanizing the paper’s straight-wall read–write gadgets, where walls
are line segments of slope `±1` (hence constant normals).
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open scoped RealInnerProductSpace

/-- An affine line in `ℝ²` specified by a normal vector `n` and a constant `c`. -/
def Line (n : V) (c : ℝ) : Set V :=
  { q | inner ℝ n q = c }

@[simp] theorem mem_Line_iff {n : V} {c : ℝ} {q : V} : q ∈ Line n c ↔ inner ℝ n q = c := Iff.rfl

@[simp] theorem inner_add_smul (n p v : V) (t : ℝ) :
    inner ℝ n (p + t • v) = inner ℝ n p + t * inner ℝ n v := by
  -- Linearity in the second argument.
  simp [inner_add_right, inner_smul_right]

/-- Time-to-hit a line along the ray `p + t•v` (undefined if the ray is parallel to the line). -/
def timeToLine? (n p v : V) (c : ℝ) : Option ℝ :=
  if h : inner ℝ n v = 0 then none else some ((c - inner ℝ n p) / inner ℝ n v)

theorem timeToLine?_eq_none_iff {n p v : V} {c : ℝ} :
    timeToLine? n p v c = none ↔ inner ℝ n v = 0 := by
  classical
  unfold timeToLine?
  by_cases h : inner ℝ n v = 0
  · simp [h]
  · simp [h]

theorem timeToLine?_eq_some_iff {n p v : V} {c t : ℝ} :
    timeToLine? n p v c = some t ↔ inner ℝ n v ≠ 0 ∧ t = (c - inner ℝ n p) / inner ℝ n v := by
  classical
  unfold timeToLine?
  by_cases h : inner ℝ n v = 0
  · simp [h]
  · simp [h]

theorem mem_Line_of_timeToLine?_eq_some {n p v : V} {c t : ℝ}
    (h : timeToLine? n p v c = some t) :
    p + t • v ∈ Line n c := by
  have hv : inner ℝ n v ≠ 0 := (timeToLine?_eq_some_iff (n := n) (p := p) (v := v) (c := c) (t := t)).1 h |>.1
  have ht : t = (c - inner ℝ n p) / inner ℝ n v :=
    (timeToLine?_eq_some_iff (n := n) (p := p) (v := v) (c := c) (t := t)).1 h |>.2
  -- Expand and solve the line equation.
  simp [Line, inner_add_smul, ht, hv, sub_eq_add_neg, div_eq_mul_inv]
  ring_nf

end Billiards
end MirandaDynamics
end HeytingLean

