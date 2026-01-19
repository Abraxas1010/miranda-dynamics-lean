/-!
# MirandaDynamics.Billiards: computable rectangle billiard simulation (Float)

This file is **runtime-only** support for WS7’s executable-first requirements.

It implements a tiny billiard simulator in the axis-aligned unit square `[0,1]×[0,1]` using `Float`
arithmetic:
- compute the next wall hit time,
- advance position,
- apply specular reflection by flipping velocity components.

This is intentionally *not* used for proof-grade geometry (which remains `ℝ`-based and noncomputable),
but it provides a concrete executable that exercises the C backend and runtime behavior.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

namespace FloatSim

structure Vec2 where
  x : Float
  y : Float
  deriving Repr, Inhabited

def Vec2.add (a b : Vec2) : Vec2 := ⟨a.x + b.x, a.y + b.y⟩
def Vec2.smul (t : Float) (v : Vec2) : Vec2 := ⟨t * v.x, t * v.y⟩

def clamp01 (x : Float) : Float :=
  if x < 0.0 then 0.0 else if 1.0 < x then 1.0 else x

def inRect (p : Vec2) : Bool :=
  (0.0 ≤ p.x) && (p.x ≤ 1.0) && (0.0 ≤ p.y) && (p.y ≤ 1.0)

def inf : Float :=
  1.0 / 0.0

def nextTime1D (pos vel : Float) : Float :=
  if vel == 0.0 then
    inf
  else if vel > 0.0 then
    (1.0 - pos) / vel
  else
    (0.0 - pos) / vel

def abs (x : Float) : Float := if x < 0.0 then -x else x

def reflectX (v : Vec2) : Vec2 := ⟨-v.x, v.y⟩
def reflectY (v : Vec2) : Vec2 := ⟨v.x, -v.y⟩
def reflectXY (v : Vec2) : Vec2 := ⟨-v.x, -v.y⟩

/-- One collision step in the unit square. Returns an error if the state is invalid. -/
def stepRect (pos vel : Vec2) : Except String (Vec2 × Vec2) := Id.run do
  if inRect pos != true then
    return .error s!"position out of bounds: {repr pos}"
  let tx := nextTime1D pos.x vel.x
  let ty := nextTime1D pos.y vel.y
  let t := if tx < ty then tx else ty
  if t == inf then
    return .error "zero velocity (no boundary hit)"
  if t ≤ 0.0 then
    return .error s!"nonpositive step time: {t}"
  let pos' := Vec2.add pos (Vec2.smul t vel)
  let pos'' : Vec2 := ⟨clamp01 pos'.x, clamp01 pos'.y⟩
  -- Decide which wall(s) we hit (with a small tolerance).
  let eps : Float := 1e-7
  let hitX := abs (tx - t) ≤ eps
  let hitY := abs (ty - t) ≤ eps
  let vel' :=
    if hitX && hitY then reflectXY vel
    else if hitX then reflectX vel
    else if hitY then reflectY vel
    else vel
  return .ok (pos'', vel')

end FloatSim

end Billiards
end MirandaDynamics
end HeytingLean

