import HeytingLean.MirandaDynamics.Geometry.Forms.Manifold

/-!
# Tests: MirandaDynamics Euclidean forms

Proof-level smoke tests for the Euclidean differential-form wrapper.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Tests

open Geometry.Forms

section

abbrev E : Type := Fin 3 → ℝ

example :
    d (E := E) (d (E := E) (n := 1) (fun _ : E => (0 : E [⋀^Fin 1]→L[ℝ] ℝ))) = 0 := by
  have hω : ContDiff ℝ ⊤ (fun _ : E => (0 : E [⋀^Fin 1]→L[ℝ] ℝ)) := contDiff_const
  exact d_d_eq_zero (E := E) (n := 1) (ω := fun _ : E => (0 : E [⋀^Fin 1]→L[ℝ] ℝ)) hω

example :
    dWithin (E := E) (dWithin (E := E) (n := 1) (fun _ : E => (0 : E [⋀^Fin 1]→L[ℝ] ℝ)) Set.univ)
        Set.univ = 0 := by
  funext x
  have hω : ContDiffWithinAt ℝ (⊤ : WithTop ℕ∞)
      (fun _ : E => (0 : E [⋀^Fin 1]→L[ℝ] ℝ)) (Set.univ : Set E) x := by
    simpa using
      (contDiff_const.contDiffWithinAt : ContDiffWithinAt ℝ (⊤ : WithTop ℕ∞)
        (fun _ : E => (0 : E [⋀^Fin 1]→L[ℝ] ℝ)) (Set.univ : Set E) x)
  have hs : UniqueDiffOn ℝ (Set.univ : Set E) := by
    simp
  have hx : x ∈ closure (interior (Set.univ : Set E)) := by
    simp
  have hxs : x ∈ (Set.univ : Set E) := by
    simp
  simpa using
    (dWithin_dWithin_eq_zero (E := E) (n := 1)
      (ω := fun _ : E => (0 : E [⋀^Fin 1]→L[ℝ] ℝ)) (s := (Set.univ : Set E))
      (r := (⊤ : WithTop ℕ∞)) (x := x) hω (by simp) hs hx hxs)

end

end Tests
end MirandaDynamics
end HeytingLean
