import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# MirandaDynamics.Billiards: specular reflection (core)

This file sets up a minimal, reusable core for billiard dynamics: **specular reflection** of a
velocity vector across a (codimension-one) tangent subspace.

We reuse Mathlib’s `Submodule.reflection`, which produces a `LinearIsometryEquiv` and therefore
immediately gives:
- involutivity (`reflect (reflect v) = v`),
- norm preservation (`‖reflect v‖ = ‖v‖`),
- fixed-point characterization (`reflect v = v ↔ v ∈ K`).

This is a small but concrete foundation for WS7 (billiard geometry), independent of choosing a
particular class of billiard tables.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open scoped RealInnerProductSpace

/-- A concrete model of `ℝ²` as a real inner product space. -/
abbrev V : Type := EuclideanSpace ℝ (Fin 2)

/-- Specular reflection across the hyperplane orthogonal to the normal vector `n`.

Concretely, this reflects across the tangent subspace `((ℝ ∙ n)ᗮ : Submodule ℝ V)`. -/
noncomputable def reflect (n : V) : V ≃ₗᵢ[ℝ] V :=
  ((ℝ ∙ n)ᗮ).reflection

theorem reflect_apply (n v : V) :
    reflect n v = v - 2 • ((inner ℝ n v) / ((‖n‖ : ℝ) ^ 2)) • n := by
  -- Unfold `reflect` and reduce to the standard formula for reflection in a 1D subspace.
  dsimp [reflect]
  -- Reflection in `Kᗮ` is the negative of reflection in `K`.
  have horth :
      ((ℝ ∙ n : Submodule ℝ V)ᗮ).reflection v =
        -((ℝ ∙ n : Submodule ℝ V).reflection v) := by
    simpa using (Submodule.reflection_orthogonal_apply (K := (ℝ ∙ n : Submodule ℝ V)) (v := v))
  -- Reflection in a 1D subspace has an explicit inner-product formula.
  -- Combine the two identities and simplify.
  rw [horth]
  simp [Submodule.reflection_singleton_apply, sub_eq_add_neg, add_comm, two_smul]

@[simp] theorem reflect_reflect (n v : V) : reflect n (reflect n v) = v := by
  simp [reflect]

@[simp] theorem norm_reflect (n v : V) : ‖reflect n v‖ = ‖v‖ := by
  dsimp [reflect]
  exact (((ℝ ∙ n)ᗮ).reflection.norm_map v)

theorem reflect_eq_self_iff (n v : V) : reflect n v = v ↔ v ∈ (ℝ ∙ n : Submodule ℝ V)ᗮ := by
  simpa [reflect] using (Submodule.reflection_eq_self_iff (K := (ℝ ∙ n : Submodule ℝ V)ᗮ) (x := v))

@[simp] theorem reflect_normal_eq_neg (n : V) : reflect n n = -n := by
  simpa [reflect] using (Submodule.reflection_orthogonalComplement_singleton_eq_neg (v := n))

end Billiards
end MirandaDynamics
end HeytingLean
