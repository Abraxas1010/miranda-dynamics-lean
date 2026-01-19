import HeytingLean.MirandaDynamics.Discrete.FlowBridge

/-!
# Tests: MirandaDynamics discrete flow sanity

Regression tests for the `Flow`/reaching-rel bridge over the discrete halting model.
-/

namespace HeytingLean.Tests.MirandaDynamics.DiscreteFlow

open HeytingLean.MirandaDynamics.Discrete
open Nat.Partrec

example (n : Nat) (c : Nat.Partrec.Code) :
    ReachesCycle n c ↔ HeytingLean.MirandaDynamics.Undecidability.Halting.Halts n c :=
  reachesCycle_iff_halts n c

example (n : Nat) (c : Nat.Partrec.Code) :
    ReachesCycle n c ↔ ∃ y : {s // s ∈ cycleSet}, (reachingRel_cycle n c).rel ⟨start, by simp⟩ y :=
  reachesCycle_iff_exists_reachingRel n c

end HeytingLean.Tests.MirandaDynamics.DiscreteFlow
