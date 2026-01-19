import HeytingLean.MirandaDynamics.Billiards.GeometryDeterministicNext
import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteCollisionRewrite

/-!
# MirandaDynamics.Billiards: minimal-time deterministic `next?` for a chosen rewrite wall (WS7.3)

This is the deterministic/minimal-time analogue of `PaperReadWriteCollisionRewrite`:

* fix a single rewrite wall segment `rwWallRewrite k ds cur`,
* start a vertical ray from `y=0` at `x=x0`,
* prove there is a unique first-hit time, and compute it explicitly.

This remains corridor-local and does **not** address “no spurious collisions” across the infinite
wall unions (the long-horizon WS7.3 gap).
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set
open Plane

namespace PaperReadWrite

open Table
open Table.DeterministicNext

namespace RewriteDeterministic

structure Entry where
  k : ℤ
  ds : List Bool
  cur : Bool
  x0 : ℝ
  hx0 : x0 ∈ rwBlockInterval k ds

def startPos (e : Entry) : V := Plane.mk e.x0 0
def startVel (_e : Entry) : V := eY
def startState (e : Entry) : Billiards.State := ⟨startPos e, startVel e⟩

def table (e : Entry) : Billiards.Table :=
  { inside := Set.univ
    boundary := rwWallRewrite e.k e.ds e.cur
    normal := fun _ => rwWallRewriteNormal e.k e.ds e.cur }

def hitTime (e : Entry) : ℝ :=
  if e.cur
  then 2 + rewriteSlope e.k e.ds * (e.x0 - rwBlockCenter e.k e.ds)
  else 2 + rewriteSlope e.k e.ds * (rwBlockCenter e.k e.ds - e.x0)

theorem hitTime_pos (e : Entry) : 0 < hitTime e := by
  have hm0 : 0 ≤ rewriteSlope e.k e.ds := by
    -- `rewriteSlope = 1/(1+len)` and `len>0`.
    have hlen : 0 < rwBlockLen e.k e.ds := rwBlockLen_pos e.k e.ds
    have : 0 < (1 : ℝ) + rwBlockLen e.k e.ds := by linarith
    have : 0 < rewriteSlope e.k e.ds := by
      simp [rewriteSlope, one_div, inv_pos.2 this]
    exact le_of_lt this
  cases e.cur <;> simp [hitTime, hm0]

def hitPoint (e : Entry) : V :=
  Table.DeterministicNext.hitPoint (table e) (startState e) (hitTime e)

theorem hitPoint_eq_mk (e : Entry) :
    hitPoint e = Plane.mk e.x0 (hitTime e) := by
  simp [hitPoint, Table.DeterministicNext.hitPoint, table, startState, startPos, startVel, Plane.mk, Plane.eY]

theorem hitPoint_mem_boundary (e : Entry) : hitPoint e ∈ (table e).boundary := by
  -- `x` is constant `x0`, and `y = hitTime`.
  have hx : x (hitPoint e) ∈ rwBlockInterval e.k e.ds := by
    simpa [hitPoint_eq_mk] using e.hx0
  cases hcur : e.cur <;>
    -- Unfold `rwWallRewrite` at the computed point.
    simp [table, hitPoint_eq_mk, rwWallRewrite, hx, hitTime, hcur, Plane.mk, Plane.x, Plane.y] <;>
    ring_nf

theorem no_boundary_hit_before_hitTime (e : Entry) {t : ℝ} (ht0 : 0 < t) (htlt : t < hitTime e) :
    Table.DeterministicNext.hitPoint (table e) (startState e) t ∉ (table e).boundary := by
  intro hmem
  -- Membership forces the `y`-coordinate equation, but along the vertical ray `y = t`.
  have hyTraj : y (Table.DeterministicNext.hitPoint (table e) (startState e) t) = t := by
    simp [Table.DeterministicNext.hitPoint, startState, startPos, startVel, Plane.y, Plane.mk, Plane.eY]
  have hxTraj : x (Table.DeterministicNext.hitPoint (table e) (startState e) t) = e.x0 := by
    simp [Table.DeterministicNext.hitPoint, startState, startPos, startVel, Plane.x, Plane.mk, Plane.eY]
  -- Extract the wall equation.
  have hyWall :
      y (Table.DeterministicNext.hitPoint (table e) (startState e) t) =
        (2 : ℝ) +
          (if e.cur then (rewriteSlope e.k e.ds) * (-rwBlockCenter e.k e.ds + x (Table.DeterministicNext.hitPoint (table e) (startState e) t))
           else (rewriteSlope e.k e.ds) * (rwBlockCenter e.k e.ds - x (Table.DeterministicNext.hitPoint (table e) (startState e) t))) := by
    simpa [table, rwWallRewrite] using (show Table.DeterministicNext.hitPoint (table e) (startState e) t ∈ rwWallRewrite e.k e.ds e.cur from hmem) |>.2
  -- Solve `t = hitTime e`.
  have : t = hitTime e := by
    cases hcur : e.cur <;> simp [hyTraj, hxTraj, hyWall, hitTime, hcur] <;> ring_nf
  exact (not_lt_of_eq this) htlt

theorem isFirstHitTime_hitTime (e : Entry) :
    Table.DeterministicNext.IsFirstHitTime (table e) (startState e) (hitTime e) := by
  refine And.intro ?hit ?noEarlier
  · refine And.intro (hitTime_pos e) ?_
    refine And.intro ?mem ?seg
    · simpa [hitPoint, Table.DeterministicNext.hitPoint] using hitPoint_mem_boundary e
    · -- `inside = univ`, so segment condition is trivial.
      simp [table]
  · intro t ht0 htlt
    exact no_boundary_hit_before_hitTime e ht0 htlt

theorem start_Good_firstHit (e : Entry) :
    Table.DeterministicNext.Good (table e) (startState e) := by
  classical
  refine ExistsUnique.intro (hitTime e) (isFirstHitTime_hitTime e) ?_
  intro t htFirst
  have htpos : 0 < t := htFirst.1.1.1
  -- Show `t ≤ hitTime e`: otherwise `hitTime e` would be an earlier boundary hit.
  have htle : t ≤ hitTime e := by
    by_contra hgt
    have hlt : hitTime e < t := lt_of_not_ge hgt
    have hmem : Table.DeterministicNext.hitPoint (table e) (startState e) (hitTime e) ∈ (table e).boundary :=
      (isFirstHitTime_hitTime e).1.2.1
    exact (htFirst.2 (hitTime e) (hitTime_pos e) hlt) hmem
  -- Show `¬t < hitTime e` using the no-earlier-hit property for `t`.
  have hnot : ¬t < hitTime e := by
    intro hlt
    have hmem : Table.DeterministicNext.hitPoint (table e) (startState e) t ∈ (table e).boundary :=
      (htFirst.1.1.2).1
    exact no_boundary_hit_before_hitTime e htpos hlt hmem
  exact le_antisymm htle (le_of_not_gt hnot)

theorem next?_eq_some (e : Entry) :
    Table.DeterministicNext.next? (table e) (startState e) =
      some ⟨hitPoint e, reflect (rwWallRewriteNormal e.k e.ds e.cur) eY⟩ := by
  classical
  have hgood : Table.DeterministicNext.Good (table e) (startState e) := start_Good_firstHit e
  -- Unfold `next?` and pin down the chosen first-hit time using uniqueness.
  unfold Table.DeterministicNext.next?
  split_ifs with h
  · let t : ℝ := Classical.choose (ExistsUnique.exists h)
    have htFirst : Table.DeterministicNext.IsFirstHitTime (table e) (startState e) t :=
      (Classical.choose_spec (ExistsUnique.exists h)).1
    have htEq : t = hitTime e := by
      exact ExistsUnique.unique h htFirst (isFirstHitTime_hitTime e)
    subst htEq
    simp [hitPoint, Table.DeterministicNext.hitPoint, table, startState, startPos, startVel]
  · exact (hgood h).elim

end RewriteDeterministic

end PaperReadWrite

end Billiards
end MirandaDynamics
end HeytingLean

