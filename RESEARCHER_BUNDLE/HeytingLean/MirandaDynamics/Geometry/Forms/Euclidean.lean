import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# MirandaDynamics.Geometry.Forms: Euclidean differential forms (starter layer)

Mathlib currently provides a robust definition of differential forms and the exterior derivative on
**normed spaces**. For the “full completion” Miranda/fluids track, we will eventually want forms on
manifolds; however, the manifold-level API is not turnkey yet.

This file provides a small Euclidean-facing wrapper:
- an `n`-form is an unbundled function `E → E[⋀^Fin n]→L[ℝ] ℝ`;
- `d` is `extDeriv`;
- we expose the standard `d ∘ d = 0` lemma from Mathlib in this wrapper namespace.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Geometry
namespace Forms

open scoped Topology

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Unbundled `n`-forms on a real normed space `E`. -/
abbrev Form (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) : Type (max u 0) :=
  E → E [⋀^Fin n]→L[ℝ] ℝ

/-- Exterior derivative of an unbundled form. -/
noncomputable def d {n : ℕ} (ω : Form (E := E) n) : Form (E := E) (n + 1) :=
  fun x => extDeriv ω x

theorem d_def {n : ℕ} (ω : Form (E := E) n) : d (E := E) ω = fun x => extDeriv ω x :=
  rfl

/-- `d (d ω) = 0` for sufficiently smooth differential forms (re-export of Mathlib). -/
theorem d_d_eq_zero {n : ℕ} (ω : Form (E := E) n) (hω : ContDiff ℝ ⊤ ω) :
    d (E := E) (d (E := E) ω) = 0 := by
  -- `extDeriv (extDeriv ω) = 0` is Mathlib's theorem `extDeriv_extDeriv`.
  have h : extDeriv (extDeriv ω) = 0 := extDeriv_extDeriv (ω := ω) (r := (⊤ : WithTop ℕ∞)) hω (by simp)
  funext x
  exact congrArg (fun f => f x) h

end Forms
end Geometry
end MirandaDynamics
end HeytingLean
