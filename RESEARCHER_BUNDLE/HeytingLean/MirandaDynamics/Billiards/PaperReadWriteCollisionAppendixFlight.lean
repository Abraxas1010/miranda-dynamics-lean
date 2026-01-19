import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteCollision
import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteFlightAvoidance

/-!
# MirandaDynamics.Billiards: Appendix-consistent straight-gadget collision cross-section (WS7.3)

The existing `PaperReadWriteCollision` file models a *toy* cross-section: a vertical incoming ray
hits a selected `rwWall` and reflects horizontally.  The Appendix “no spurious collisions” argument,
however, reasons about **diagonal extremal rays** (`flightRayLeft0`, `flightRayRight1`) through the
*upper endpoints* of wall segments.

This file introduces a second, Appendix-consistent collision-space convention for the straight
read-only gadget, without modifying the toy model:

* a state is a chosen wall segment `rwWall k ds cur`;
* the cross-section point is the **upper endpoint** of that segment;
* the outgoing direction is the diagonal extremal ray used by the Appendix.

Downstream “avoidance” theorems can then be stated directly about the actual trajectory set
`traj s ⊆ flightRay…`.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set
open Plane

namespace PaperReadWrite

namespace AppendixStraight

/-- Appendix-style collision-space state for a straight read-only wall segment. -/
structure State where
  k : ℤ
  ds : List Bool
  cur : Bool

/-- The `y`-coordinate of the (upper) endpoints of `rwWall k ds cur`. -/
noncomputable def endpointY (k : ℤ) (ds : List Bool) : ℝ :=
  (2 : ℝ) + (rwBlockLen k ds) / 2

/-- The **upper endpoint** of `rwWall k ds cur` used by the Appendix extremal-flight argument:
left endpoint when `cur=false`, right endpoint when `cur=true`. -/
def upperEndpoint (s : State) : V :=
  if s.cur then
    Plane.mk (rwBlockLeft s.k s.ds + rwBlockLen s.k s.ds) (endpointY s.k s.ds)
  else
    Plane.mk (rwBlockLeft s.k s.ds) (endpointY s.k s.ds)

/-- The Appendix extremal outgoing velocity from `upperEndpoint`:
down-left when `cur=false`, down-right when `cur=true`. -/
def vel (s : State) : V :=
  if s.cur then (eX - eY) else -(eX + eY)

/-- The corresponding Appendix extremal ray-set (`flightRay…`) for the state. -/
def flightRay (s : State) : Set V :=
  if s.cur then flightRayRight1 s.k s.ds else flightRayLeft0 s.k s.ds

/-- The actual trajectory set starting at `upperEndpoint` and moving along `vel`. -/
def traj (s : State) : Set V :=
  {q | ∃ t : ℝ, 0 ≤ t ∧ q = upperEndpoint s + t • vel s}

theorem upperEndpoint_mem_rwWall (s : State) : upperEndpoint s ∈ rwWall s.k s.ds s.cur := by
  have hlen : 0 ≤ rwBlockLen s.k s.ds := le_of_lt (rwBlockLen_pos s.k s.ds)
  have hcenter : rwBlockCenter s.k s.ds = rwBlockLeft s.k s.ds + (rwBlockLen s.k s.ds) / 2 := by
    simp [rwBlockCenter]
  cases hcur : s.cur <;> simp [upperEndpoint, endpointY, rwWall, rwBlockInterval, hcur, hcenter, hlen] <;> ring_nf

theorem traj_subset_flightRay (s : State) : traj s ⊆ flightRay s := by
  intro q hq
  rcases hq with ⟨t, ht0, rfl⟩
  cases hcur : s.cur
  · -- `cur=false`: move down-left along `flightRayLeft0`.
    have hx :
        x (upperEndpoint s + t • vel s) ≤ rwBlockLeft s.k s.ds := by
      -- `x = left - t`.
      simp [upperEndpoint, vel, hcur, Plane.x, Plane.eX, Plane.eY, Plane.mk, ht0]
    have hline :
        upperEndpoint s + t • vel s ∈ flightLineLeft0 s.k s.ds := by
      -- `y - x` stays constant along direction `(-1,-1)` and matches the endpoint constant.
      have :
          y (upperEndpoint s + t • vel s) - x (upperEndpoint s + t • vel s) =
            (2 : ℝ) + (rwBlockLen s.k s.ds) / 2 - rwBlockLeft s.k s.ds := by
        simp [upperEndpoint, endpointY, vel, hcur, Plane.x, Plane.y, Plane.eX, Plane.eY, Plane.mk]
        ring_nf
      simpa [flightLineLeft0] using this
    refine ?_
    -- Package as `flightRayLeft0 = flightLineLeft0 ∩ {x ≤ left}`.
    simpa [flightRay, flightRayLeft0, hcur] using And.intro hline hx
  · -- `cur=true`: move down-right along `flightRayRight1`.
    have hx :
        rwBlockLeft s.k s.ds + rwBlockLen s.k s.ds ≤ x (upperEndpoint s + t • vel s) := by
      -- `x = right + t`.
      simp [upperEndpoint, vel, hcur, Plane.x, Plane.eX, Plane.eY, Plane.mk, ht0]
    have hline :
        upperEndpoint s + t • vel s ∈ flightLineRight1 s.k s.ds := by
      have :
          y (upperEndpoint s + t • vel s) + x (upperEndpoint s + t • vel s) =
            (2 : ℝ) + (rwBlockLen s.k s.ds) / 2 + (rwBlockLeft s.k s.ds + rwBlockLen s.k s.ds) := by
        simp [upperEndpoint, endpointY, vel, hcur, Plane.x, Plane.y, Plane.eX, Plane.eY, Plane.mk]
        ring_nf
      simpa [flightLineRight1] using this
    simpa [flightRay, flightRayRight1, hcur] using And.intro hline hx

end AppendixStraight

end PaperReadWrite

end Billiards
end MirandaDynamics
end HeytingLean

