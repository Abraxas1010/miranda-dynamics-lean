import Mathlib.Dynamics.Flow
import HeytingLean.MirandaDynamics.TKFT.Reaching

/-!
# MirandaDynamics.TKFT: reaching relations induced by Mathlib flows

TKFT’s “reaching semantics” is defined using dynamical evolution from an input boundary to an output
boundary. Re-formalizing the full bordism+vector-field story is out of scope here, but Mathlib
already provides an abstract notion of a **flow** as a continuous monoid action.

This file defines a *generic* reaching relation induced by a flow and designated input/output sets:

- objects: subtypes `{x // x ∈ In}` and `{y // y ∈ Out}`,
- morphism: `x ↝ y` iff there exists a time `t` with `ϕ t x = y`.

No uniqueness is assumed; this stays at the relation level.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace TKFT

open Set

universe u

section

variable {τ : Type u} [AddMonoid τ] [TopologicalSpace τ] [ContinuousAdd τ]
variable {α : Type u} [TopologicalSpace α]

/-- The reaching relation induced by a flow `ϕ` between designated subsets `In` and `Out`. -/
def reachingRelOfFlow (ϕ : Flow τ α) (In Out : Set α) :
    ReachingRel {x // x ∈ In} {y // y ∈ Out} :=
  ⟨fun x y => ∃ t : τ, ϕ t x.1 = y.1⟩

theorem reachingRelOfFlow_spec (ϕ : Flow τ α) (In Out : Set α) (x : {x // x ∈ In}) (y : {y // y ∈ Out}) :
    (reachingRelOfFlow (ϕ := ϕ) In Out).rel x y ↔ ∃ t : τ, ϕ t x.1 = y.1 :=
  Iff.rfl

/-- Flow-induced reaching respects time-addition: composing two reaches along an intermediate set
gives a reach to the final set (by taking `t₁ + t₂`). -/
theorem reachingRelOfFlow_comp (ϕ : Flow τ α) (In Mid Out : Set α) (x : {x // x ∈ In}) (z : {y // y ∈ Out}) :
    (ReachingRel.comp (reachingRelOfFlow (ϕ := ϕ) In Mid) (reachingRelOfFlow (ϕ := ϕ) Mid Out)).rel x z →
      (reachingRelOfFlow (ϕ := ϕ) In Out).rel x z := by
  rintro ⟨y, ⟨t₂, ht₂⟩, ⟨t₁, ht₁⟩⟩
  refine ⟨t₁ + t₂, ?_⟩
  -- `ϕ (t₁+t₂) x = ϕ t₁ (ϕ t₂ x) = ϕ t₁ y = z`.
  calc
    ϕ (t₁ + t₂) x.1 = ϕ t₁ (ϕ t₂ x.1) := by simpa using (Flow.map_add (ϕ := ϕ) t₁ t₂ x.1)
    _ = ϕ t₁ y.1 := by simp [ht₂]
    _ = z.1 := ht₁

end

end TKFT
end MirandaDynamics
end HeytingLean
