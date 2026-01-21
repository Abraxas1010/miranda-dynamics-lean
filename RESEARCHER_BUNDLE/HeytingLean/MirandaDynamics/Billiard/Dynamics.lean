import HeytingLean.MirandaDynamics.Billiard.Basic

/-!
# MirandaDynamics.Billiard: executable dynamics

This file provides a small, deterministic evolution function for 1D billiards.

Note: this is intended primarily as an *executable calibration target*; it does not attempt a
machine-checked reversibility theorem for floating-point evolution.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Billiard

/-- 1D elastic collision update (conservation of momentum + kinetic energy). -/
def collide (b1 b2 : Ball) : Ball × Ball :=
  let m1 := b1.mass
  let m2 := b2.mass
  let v1 := b1.vel
  let v2 := b2.vel
  let v1' := ((m1 - m2) * v1 + 2.0 * m2 * v2) / (m1 + m2)
  let v2' := ((m2 - m1) * v2 + 2.0 * m1 * v1) / (m1 + m2)
  ({ b1 with vel := v1' }, { b2 with vel := v2' })

def reflectWalls (tbl : Table) (b : Ball) : Ball :=
  if b.pos < tbl.left then
    { b with pos := tbl.left + (tbl.left - b.pos), vel := -b.vel }
  else if b.pos > tbl.right then
    { b with pos := tbl.right - (b.pos - tbl.right), vel := -b.vel }
  else
    b

def advanceBall (dt : Float) (tbl : Table) (b : Ball) : Ball :=
  reflectWalls tbl { b with pos := b.pos + b.vel * dt }

def evolveSteps (tbl : Table) : Nat → Float → Array Ball → Array Ball
  | 0, _, bs => bs
  | n + 1, dt, bs =>
      evolveSteps tbl n dt (bs.map (advanceBall dt tbl))

/-- Deterministic time evolution using a fixed step size (wall reflections only). -/
def evolve (state : BilliardState) (t : Float) (dt : Float := 0.001) : BilliardState :=
  if t <= 0 then
    state
  else
    let dt := if dt <= 0 then 0.001 else dt
    let steps : Nat := UInt64.toNat ((t / dt).toUInt64)
    let rem : Float := t - (Float.ofNat steps) * dt
    let bs := evolveSteps state.table steps dt state.balls
    let bs := if rem <= 0 then bs else bs.map (advanceBall rem state.table)
    { state with balls := bs, time := state.time + t }

end Billiard
end MirandaDynamics
end HeytingLean
