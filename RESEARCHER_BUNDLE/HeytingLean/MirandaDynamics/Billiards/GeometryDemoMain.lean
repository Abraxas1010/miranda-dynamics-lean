import HeytingLean.MirandaDynamics.Billiards.FloatSim

/-!
# miranda_billiards_geometry_demo

Computable runtime demo for WS7: simulates a few specular reflections in the unit square using
`Float` arithmetic.

No file IO is performed; this should not crash under hostile env/PATH QA tests.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

namespace GeometryDemo

open FloatSim

def showState (p v : Vec2) : String :=
  s!"pos={repr p} vel={repr v}"

def loop (fuel : Nat) (p v : Vec2) : IO Unit := do
  IO.println s!"[step {fuel}] {showState p v}"
  match fuel with
  | 0 => pure ()
  | Nat.succ n =>
    match FloatSim.stepRect p v with
    | .error e =>
      IO.println s!"[error] {e}"
    | .ok (p', v') =>
      loop n p' v'

def main (_argv : List String) : IO UInt32 := do
  IO.println "[miranda_billiards_geometry_demo] rectangle billiard simulation (Float)"
  let p0 : Vec2 := ⟨0.2, 0.3⟩
  let v0 : Vec2 := ⟨0.37, 0.21⟩
  loop 12 p0 v0
  return 0

end GeometryDemo

end Billiards
end MirandaDynamics
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.MirandaDynamics.Billiards.GeometryDemo.main args
