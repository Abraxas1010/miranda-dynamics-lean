import HeytingLean.MirandaDynamics.Dynamics.PartialFlow
import HeytingLean.MirandaDynamics.Dynamics.PartialFlowOfFlow
import HeytingLean.MirandaDynamics.TKFT.Reaching
import HeytingLean.MirandaDynamics.TKFT.FlowReaching

/-!
# MirandaDynamics.TKFT: reaching relations induced by partial flows

This file generalizes `TKFT.reachingRelOfFlow` from global `Flow` to a minimal “partial flow” notion.

The key point is that a partial flow carries explicit domain witnesses, so reachability must carry
those witnesses too.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace TKFT

open MirandaDynamics

universe u

namespace PartialFlow

variable {τ : Type u} [AddMonoid τ]
variable {α : Type u}

/-- The reaching relation induced by a partial flow between designated subsets `In` and `Out`. -/
def reachingRelOfPartialFlow (ϕ : Dynamics.PartialFlow τ α) (In Out : Set α) :
    ReachingRel {x // x ∈ In} {y // y ∈ Out} :=
  ⟨fun x y => ∃ t : τ, ϕ.dom t x.1 ∧ ϕ.map t x.1 = y.1⟩

theorem reachingRelOfPartialFlow_spec (ϕ : Dynamics.PartialFlow τ α) (In Out : Set α)
    (x : {x // x ∈ In}) (y : {y // y ∈ Out}) :
    (reachingRelOfPartialFlow (ϕ := ϕ) In Out).rel x y ↔
      ∃ t : τ, ϕ.dom t x.1 ∧ ϕ.map t x.1 = y.1 :=
  Iff.rfl

/-- Partial-flow reachability composes along time-addition (with domain side-conditions supplied by `ϕ`). -/
theorem reachingRelOfPartialFlow_comp (ϕ : Dynamics.PartialFlow τ α) (In Mid Out : Set α)
    (x : {x // x ∈ In}) (z : {y // y ∈ Out}) :
    (ReachingRel.comp (reachingRelOfPartialFlow (ϕ := ϕ) In Mid)
        (reachingRelOfPartialFlow (ϕ := ϕ) Mid Out)).rel x z →
      (reachingRelOfPartialFlow (ϕ := ϕ) In Out).rel x z := by
  rintro ⟨y, ⟨t₂, ht₂, ht₂eq⟩, ⟨t₁, ht₁, ht₁eq⟩⟩
  have ht₁' : ϕ.dom t₁ (ϕ.map t₂ x.1) := ht₂eq.symm ▸ ht₁
  have htadd : ϕ.dom (t₁ + t₂) x.1 := ϕ.dom_add t₁ t₂ x.1 ht₂ ht₁'
  refine ⟨t₁ + t₂, htadd, ?_⟩
  calc
    ϕ.map (t₁ + t₂) x.1 = ϕ.map t₁ (ϕ.map t₂ x.1) := by
      exact ϕ.map_add t₁ t₂ x.1 ht₂ ht₁'
    _ = ϕ.map t₁ y.1 := by simp [ht₂eq]
    _ = z.1 := ht₁eq

/-- For a global `Flow`, the partial-flow reaching relation reduces to `reachingRelOfFlow`. -/
theorem reachingRelOfPartialFlow_ofFlow_eq
    [TopologicalSpace τ] [ContinuousAdd τ] [TopologicalSpace α]
    (ϕ : Flow τ α) (In Out : Set α) :
    reachingRelOfPartialFlow (ϕ := Dynamics.PartialFlow.ofFlow (τ := τ) (α := α) ϕ) In Out =
      reachingRelOfFlow (ϕ := ϕ) In Out := by
  ext x y
  constructor
  · rintro ⟨t, _ht, hEq⟩
    exact ⟨t, hEq⟩
  · rintro ⟨t, hEq⟩
    exact ⟨t, True.intro, hEq⟩

end PartialFlow

end TKFT
end MirandaDynamics
end HeytingLean
