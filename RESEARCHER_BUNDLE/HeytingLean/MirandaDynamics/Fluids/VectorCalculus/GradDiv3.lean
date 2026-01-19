import HeytingLean.MirandaDynamics.Fluids.VectorCalculus.Curl3
import Mathlib.LinearAlgebra.CrossProduct

/-!
# MirandaDynamics.Fluids.VectorCalculus: grad/div and a steady Euler shell on `ℝ³`

This file continues the Euclidean staging work for the fluids track:

- `grad` and `div` are defined on `ℝ³ := Fin 3 → ℝ` using `fderiv` and the coordinate basis;
- a minimal *steady Euler (Bernoulli/Lamb form) shell* is provided as an equation
  `u × curl u = ∇p` (no PDE theory claimed).

This is enough to write and sanity-check downstream “if a construction produces a Beltrami field,
then it produces a steady Euler solution” statements, while deferring analytic content.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Fluids
namespace VectorCalculus

open scoped BigOperators Matrix

namespace R3

open R3

private abbrev i0 : Fin 3 := ⟨0, by decide⟩
private abbrev i1 : Fin 3 := ⟨1, by decide⟩
private abbrev i2 : Fin 3 := ⟨2, by decide⟩

/-- Coordinate gradient of a scalar field `f : ℝ³ → ℝ`. -/
noncomputable def grad (f : V → ℝ) (x : V) : V :=
  ![dcoord f x i0, dcoord f x i1, dcoord f x i2]

/-- Coordinate divergence of a vector field `u : ℝ³ → ℝ³`. -/
noncomputable def div (u : V → V) (x : V) : ℝ :=
  ∑ i : Fin 3, dcoord (fun y => u y i) x i

theorem grad_const (c : ℝ) (x : V) : grad (fun _ => c) x = 0 := by
  ext i
  fin_cases i <;> simp [grad, dcoord, basisVec]

theorem div_const (c : V) (x : V) : div (fun _ => c) x = 0 := by
  simp [div, dcoord, basisVec]

/-- A minimal steady Euler “shell” (Bernoulli/Lamb form): `u × curl u = ∇p` pointwise.

This is a *definition only* (no existence/regularity theorems). -/
def IsEulerSteadyBernoulli (u : V → V) (p : V → ℝ) : Prop :=
  ∀ x : V, (u x) ⨯₃ (curl u x) = grad p x

theorem eulerSteadyBernoulli_const (c : V) :
    IsEulerSteadyBernoulli (u := fun _ => c) (p := fun _ => (0 : ℝ)) := by
  intro x
  simp [curl_const, grad_const]

theorem eulerSteadyBernoulli_const_of_beltrami (u : V → V) (lam : ℝ) (h : IsBeltrami u lam) :
    IsEulerSteadyBernoulli (u := u) (p := fun _ => (0 : ℝ)) := by
  intro x
  have hxc : (u x) ⨯₃ (curl u x) = 0 := by
    calc
      (u x) ⨯₃ (curl u x) = (u x) ⨯₃ (lam • u x) := by simp [h x]
      _ = lam • ((u x) ⨯₃ (u x)) := by
        exact (LinearMap.map_smul (crossProduct (R := ℝ) (u x)) lam (u x))
      _ = 0 := by
        simp
  simp [grad_const, hxc]

end R3

end VectorCalculus
end Fluids
end MirandaDynamics
end HeytingLean
