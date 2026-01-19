import Mathlib.Dynamics.Flow
import HeytingLean.MirandaDynamics.Dynamics.PartialFlow

/-!
# MirandaDynamics.Dynamics: `Flow` as a `PartialFlow`

This file isolates the bridge from Mathlib’s global `Flow` to our topology-free `PartialFlow`.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Dynamics

universe u v

namespace PartialFlow

variable {τ : Type u} {α : Type v}
variable [AddMonoid τ] [TopologicalSpace τ] [ContinuousAdd τ]
variable [TopologicalSpace α]

/-- A global `Flow` is a `PartialFlow` with domain `True`. -/
def ofFlow (ϕ : Flow τ α) : Dynamics.PartialFlow τ α where
  dom := fun _ _ => True
  map := fun t x => ϕ t x
  dom_zero := fun _ => True.intro
  map_zero := by
    intro x
    have h : ϕ 0 x = id x := congrArg (fun f => f x) (Flow.map_zero (ϕ := ϕ))
    exact h.trans rfl
  dom_add := by
    intro _t₁ _t₂ _x _ht₂ _ht₁
    exact True.intro
  map_add := by
    intro t₁ t₂ x _ht₂ _ht₁
    exact Flow.map_add (ϕ := ϕ) t₁ t₂ x

@[simp] theorem ofFlow_dom (ϕ : Flow τ α) (t : τ) (x : α) :
    (ofFlow (τ := τ) (α := α) ϕ).dom t x :=
  True.intro

@[simp] theorem ofFlow_map (ϕ : Flow τ α) (t : τ) (x : α) :
    (ofFlow (τ := τ) (α := α) ϕ).map t x = ϕ t x := by
  rfl

end PartialFlow

end Dynamics
end MirandaDynamics
end HeytingLean
