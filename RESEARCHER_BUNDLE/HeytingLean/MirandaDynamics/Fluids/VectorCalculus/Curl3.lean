import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# MirandaDynamics.Fluids.VectorCalculus: a coordinate curl on `ℝ³`

Mathlib does not currently expose a turnkey `curl` operator suitable for the Euler/Beltrami track.
As a staged step towards WS4/WS5, this file defines a **coordinate** curl operator on `ℝ³` modeled
as `Fin 3 → ℝ`, using Fréchet derivatives (`fderiv`).

This is intentionally minimal and Euclidean-only; later work can connect it to differential-form
definitions (via a Hodge star) when such infrastructure is available.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Fluids
namespace VectorCalculus

open scoped BigOperators

/-! Definitions specialized to a concrete model of `ℝ³` (`Fin 3 → ℝ`). -/
namespace R3

/-- A concrete model of `ℝ³`. -/
abbrev V : Type := Fin 3 → ℝ

noncomputable def basisVec (j : Fin 3) : V := Pi.single j 1

/-- Coordinate directional derivative at `x` along the basis direction `j`. -/
noncomputable def dcoord (f : V → ℝ) (x : V) (j : Fin 3) : ℝ :=
  (fderiv ℝ f x) (basisVec j)

@[simp] theorem basisVec_apply_self (j : Fin 3) : basisVec j j = (1 : ℝ) := by
  simp [basisVec]

@[simp] theorem basisVec_apply_ne {i j : Fin 3} (h : i ≠ j) : basisVec j i = (0 : ℝ) := by
  simp [basisVec, h]

private abbrev i0 : Fin 3 := ⟨0, by decide⟩
private abbrev i1 : Fin 3 := ⟨1, by decide⟩
private abbrev i2 : Fin 3 := ⟨2, by decide⟩

/-- Coordinate curl of a vector field `u : ℝ³ → ℝ³`. -/
noncomputable def curl (u : V → V) (x : V) : V :=
  ![
    dcoord (fun y => u y i2) x i1 - dcoord (fun y => u y i1) x i2,
    dcoord (fun y => u y i0) x i2 - dcoord (fun y => u y i2) x i0,
    dcoord (fun y => u y i1) x i0 - dcoord (fun y => u y i0) x i1
  ]

theorem curl_const (c : V) (x : V) : curl (fun _ => c) x = 0 := by
  ext i
  fin_cases i <;> simp [curl, dcoord, basisVec]

/-- `u` is a Beltrami field with factor `λ` if `curl u = λ u` pointwise. -/
def IsBeltrami (u : V → V) (lam : ℝ) : Prop :=
  ∀ x : V, curl u x = lam • u x

end R3

end VectorCalculus
end Fluids
end MirandaDynamics
end HeytingLean
