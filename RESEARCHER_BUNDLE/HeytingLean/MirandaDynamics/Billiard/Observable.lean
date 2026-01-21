import HeytingLean.MirandaDynamics.Billiard.Basic

/-!
# MirandaDynamics.Billiard: observation model

This file defines a simple observation process (rounding to a fixed decimal precision).
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Billiard

/-- Observation parameters (these are what we calibrate). -/
structure ObservationParams where
  positionPrecision : Nat
  timePrecision : Nat
  deriving Repr

def roundTo (x : Float) (decimals : Nat) : Float :=
  let factor := Float.pow 10.0 (Float.ofNat decimals)
  (x * factor).round / factor

/-- Apply the observation process to the true state. -/
def observe (params : ObservationParams) (state : BilliardState) : Observation :=
  {
    positions := state.balls.map (fun b => roundTo b.pos params.positionPrecision)
    precision := params.positionPrecision
    timestamp := roundTo state.time params.timePrecision
  }

end Billiard
end MirandaDynamics
end HeytingLean
