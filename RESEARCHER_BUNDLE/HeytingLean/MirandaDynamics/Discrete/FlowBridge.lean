import Mathlib.Dynamics.Flow
import HeytingLean.MirandaDynamics.Discrete.HaltingToPeriodic
import HeytingLean.MirandaDynamics.TKFT.FlowReaching

/-!
# MirandaDynamics.Discrete: discrete dynamics as a Mathlib `Flow` + TKFT reaching

This file upgrades the fully-discrete halting↔periodicity bridge to the “TKFT reaching” vocabulary:

- any step function `f : α → α` gives a semiflow `Flow ℕ α` via `Flow.fromIter`,
- the flow induces a TKFT-style reaching relation between an input set and an output set,
- in our discrete halting model, **halting ↔ reaching the cycle output set**.

This is still far from billiards/Euler/Navier–Stokes geometry, but it removes one more layer of
“external claim” by relating our mechanized reduction directly to Mathlib’s flow abstraction.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Discrete

open Nat.Partrec
open Nat.Partrec.Code

/-! ## Discrete-time flow from `step` -/

local instance : TopologicalSpace State := ⊥
local instance : DiscreteTopology State := discreteTopology_bot State

noncomputable def stepFlow (n : Nat) (c : Code) : Flow Nat State :=
  Flow.fromIter (α := State) (g := step n c) (by
    simpa using (continuous_of_discreteTopology : Continuous (step n c)))

@[simp] theorem stepFlow_apply (n : Nat) (c : Code) (t : Nat) (s : State) :
    stepFlow n c t s = (step n c)^[t] s :=
  rfl

/-! ## “Reach the output boundary” predicate -/

def cycleSet : Set State :=
  {s | ∃ b : Bool, s = Sum.inr b}

def ReachesCycle (n : Nat) (c : Code) : Prop :=
  ∃ t : Nat, (step n c)^[t] start ∈ cycleSet

theorem reachesCycle_of_reachesPeriod2 (n : Nat) (c : Code) :
    ReachesPeriod2 n c → ReachesCycle n c := by
  rintro ⟨t, ht⟩
  classical
  -- Case split on the reached state.
  cases hstate : (step n c)^[t] start with
  | inl k =>
    exfalso
    have : ¬Function.IsPeriodicPt (step n c) 2 (Sum.inl k) :=
      not_periodic2_inl n c k
    exact this (by simpa [hstate] using ht)
  | inr b =>
    refine ⟨t, ?_⟩
    exact ⟨b, hstate⟩

theorem reachesPeriod2_of_reachesCycle (n : Nat) (c : Code) :
    ReachesCycle n c → ReachesPeriod2 n c := by
  rintro ⟨t, ht⟩
  rcases ht with ⟨b, hb⟩
  refine ⟨t, ?_⟩
  -- rewrite to a cycle point and use periodicity.
  simpa [hb] using (periodic2_inr n c b)

theorem reachesCycle_iff_halts (n : Nat) (c : Code) :
    ReachesCycle n c ↔ Undecidability.Halting.Halts n c := by
  constructor
  · intro h
    exact halting_of_reachesPeriod2 n c (reachesPeriod2_of_reachesCycle n c h)
  · intro h
    exact reachesCycle_of_reachesPeriod2 n c (reachesPeriod2_of_halting n c h)

/-! ## TKFT-style reaching relation induced by the flow -/

def reachingRel_cycle (n : Nat) (c : Code) :
    TKFT.ReachingRel {x // x ∈ ({start} : Set State)} {y // y ∈ cycleSet} :=
  TKFT.reachingRelOfFlow (ϕ := stepFlow n c) ({start} : Set State) cycleSet

theorem reachesCycle_iff_exists_reachingRel (n : Nat) (c : Code) :
    ReachesCycle n c ↔ ∃ y : {s // s ∈ cycleSet}, (reachingRel_cycle n c).rel ⟨start, by simp⟩ y := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨⟨(step n c)^[t] start, ht⟩, ?_⟩
    refine ⟨t, ?_⟩
    simp [stepFlow_apply]
  · rintro ⟨y, ⟨t, ht⟩⟩
    refine ⟨t, ?_⟩
    have hEq : (step n c)^[t] start = y.1 := by
      simpa [stepFlow_apply] using ht
    -- Rewrite the goal to `y.property`.
    rw [hEq]
    exact y.property

end Discrete
end MirandaDynamics
end HeytingLean
