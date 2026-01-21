/-!
# MirandaDynamics.Billiard: basic types

This namespace provides a small, executable-friendly 1D billiard model used for observation-kernel
calibration experiments.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Billiard

/-- Position on the 1D table (normalized to `[left, right]`). -/
abbrev Position := Float

/-- Velocity (positive = rightward). -/
abbrev Velocity := Float

/-- A single ball with position and velocity. -/
structure Ball where
  pos : Position
  vel : Velocity
  mass : Float := 1.0
  deriving Repr, BEq

/-- Table boundaries. -/
structure Table where
  left : Position := 0.0
  right : Position := 1.0
  deriving Repr, BEq

/-- System state: list of balls on table. -/
structure BilliardState where
  balls : Array Ball
  table : Table := {}
  time : Float := 0.0
  deriving Repr

/-- Observation with finite precision. -/
structure Observation where
  positions : Array Float
  precision : Nat
  timestamp : Float
  deriving Repr

end Billiard
end MirandaDynamics
end HeytingLean

