import HeytingLean.MirandaDynamics.Geometry.Forms.Euclidean
import Mathlib.Analysis.NormedSpace.Alternating.Curry

/-!
# MirandaDynamics.Geometry.Contact: Euclidean (pointwise) contact/Reeb conditions

Mathlib currently provides differential forms on normed spaces together with the exterior derivative
`extDeriv`. A full manifold-level contact-geometry library is not turnkey in this repo’s Mathlib pin,
so this file provides a **minimal Euclidean-facing layer**:

- a 1-form `α : Forms.Form 1` induces a 2-form `dα : Forms.Form 2`;
- we define pointwise predicates:
  - kernel nondegeneracy (a linear-algebra surrogate for “contact”),
  - Reeb equations (`α(R)=1` and `dα(R,·)=0`),
  - a uniqueness lemma for Reeb vectors under the kernel nondegeneracy hypothesis.

This is deliberately staged: it is a usable target for later WS3/WS4 work without claiming any PDE
or manifold theorems.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Geometry
namespace Contact

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Evaluate a 1-form at a point on a vector, via the underlying continuous linear map. -/
noncomputable def eval1 (α : Forms.Form (E := E) 1) (x : E) : E →L[ℝ] ℝ :=
  (ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (ι := Fin 1) (0 : Fin 1)).symm (α x)

/-- Evaluate `dα` on a pair of vectors, using the standard `Fin 2` tuple `![v, w]`. -/
noncomputable def eval_d (α : Forms.Form (E := E) 1) (x : E) (v w : E) : ℝ :=
  (Forms.d (E := E) α x) ![v, w]

@[simp] theorem eval1_apply (α : Forms.Form (E := E) 1) (x v : E) :
    eval1 (E := E) α x v = (α x) ![v] := by
  -- This is the simp lemma from `ContinuousAlternatingMap.ofSubsingleton`.
  have hvec : (fun _ : Fin 1 => v) = ![v] := by
    funext i
    cases i using Fin.cases <;> simp
  simp [eval1, hvec]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem vecCons_eq_vec2 (v w : E) :
    (Matrix.vecCons v ![w] : Fin 2 → E) = ![v, w] := by
  funext i
  cases i using Fin.cases with
  | zero =>
    simp
  | succ j =>
    cases j using Fin.cases with
    | zero =>
      simp
    | succ k =>
      exact (Fin.elim0 k)

/-- Additivity of `eval_d` in the first argument. -/
theorem eval_d_add_left (α : Forms.Form (E := E) 1) (x : E) (v₁ v₂ w : E) :
    eval_d (E := E) α x (v₁ + v₂) w = eval_d (E := E) α x v₁ w + eval_d (E := E) α x v₂ w := by
  -- rewrite everything as `vecCons` and apply multilinearity in the first variable
  simp [eval_d, vecCons_eq_vec2, ContinuousAlternatingMap.vecCons_add]

/-- Scalar multiplication of `eval_d` in the first argument. -/
theorem eval_d_smul_left (α : Forms.Form (E := E) 1) (x : E) (c : ℝ) (v w : E) :
    eval_d (E := E) α x (c • v) w = c • eval_d (E := E) α x v w := by
  simp [eval_d, vecCons_eq_vec2, ContinuousAlternatingMap.vecCons_smul]

/-- Kernel nondegeneracy at a point: if `v` is in `ker αₓ` and annihilates `ker αₓ` via `dαₓ`,
then `v = 0`. This is a linear-algebra surrogate for the contact nondegeneracy condition. -/
def NondegKer (α : Forms.Form (E := E) 1) (x : E) : Prop :=
  ∀ v : E, eval1 (E := E) α x v = 0 →
    (∀ w : E, eval1 (E := E) α x w = 0 → eval_d (E := E) α x v w = 0) → v = 0

/-- Reeb equations at a point: `α(R)=1` and `dα(R,·)=0`. -/
def IsReebAt (α : Forms.Form (E := E) 1) (x : E) (R : E) : Prop :=
  eval1 (E := E) α x R = 1 ∧ ∀ w : E, eval_d (E := E) α x R w = 0

/-- Uniqueness of Reeb vectors under the kernel-nondegeneracy hypothesis. -/
theorem reeb_unique_of_nondegKer (α : Forms.Form (E := E) 1) (x : E)
    (hND : NondegKer (E := E) α x) {R R' : E}
    (hR : IsReebAt (E := E) α x R) (hR' : IsReebAt (E := E) α x R') :
    R' = R := by
  -- Let `v := R' - R`. Show `v = 0` by kernel nondegeneracy.
  have hα0 : eval1 (E := E) α x (R' - R) = 0 := by
    simp [map_sub, hR.1, hR'.1]
  have hι0 : ∀ w : E, eval1 (E := E) α x w = 0 → eval_d (E := E) α x (R' - R) w = 0 := by
    intro w _hw
    -- expand in the first coordinate: `dα(R' - R, w) = dα(R', w) + dα(-R, w)`.
    have hSub :
        eval_d (E := E) α x (R' - R) w =
          eval_d (E := E) α x R' w + eval_d (E := E) α x (-R) w := by
      simpa [sub_eq_add_neg] using (eval_d_add_left (E := E) (α := α) (x := x) (v₁ := R') (v₂ := -R) (w := w))
    have hNeg : eval_d (E := E) α x (-R) w = - eval_d (E := E) α x R w := by
      simpa using (eval_d_smul_left (E := E) (α := α) (x := x) (c := (-1 : ℝ)) (v := R) (w := w))
    -- now use the Reeb conditions
    simp [hSub, hNeg, hR.2 w, hR'.2 w]
  have hv0 : R' - R = 0 := hND (v := R' - R) hα0 hι0
  exact sub_eq_zero.mp hv0

end Contact
end Geometry
end MirandaDynamics
end HeytingLean
