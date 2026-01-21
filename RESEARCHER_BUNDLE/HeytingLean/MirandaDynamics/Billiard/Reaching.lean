import HeytingLean.MirandaDynamics.Billiard.Dynamics
import HeytingLean.MirandaDynamics.Billiard.Observable

/-!
# MirandaDynamics.Billiard: reaching relations

This file provides a basic reachability predicate over billiard states.

In the presence of floating-point evolution, `reaches` should be interpreted as a definitional
specification rather than a decidable procedure.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Billiard

/-- True reaching: there exists a time `t` such that evolving by `t` reaches `B`. -/
def reaches (A B : BilliardState) : Prop :=
  ∃ t : Float, evolve A t = B

/-- Observable reaching: reaching holds up to the observation process. -/
def observableReaches (params : ObservationParams) (A B : BilliardState) : Prop :=
  ∃ t : Float, observe params (evolve A t) = observe params B

end Billiard
end MirandaDynamics
end HeytingLean
