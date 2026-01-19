import HeytingLean.MirandaDynamics.Billiards.GeometryDeterministicNext
import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteBoundary
import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteCollisionRewrite
import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteWallsRewriteAppendix

/-!
# MirandaDynamics.Billiards: a canonical staged “full read–write gadget” table + collision cross-section (WS7.3 scaffold)

This module provides a *staged* geometric object that matches the WS7.3 end goal’s shape:

* a billiard `Table` whose boundary is the union of the paper’s canonical read–write wall families:
  - read-only separating walls `rwWallUnionCanonical`,
  - read-only redirecting walls `tildeWallUnionCanonical`,
  - rewrite separating walls `rwWallRewriteUnionCanonical`,
  - rewrite redirecting walls `tildeWallRewriteAppendixUnionCanonical`;
* a collision-space cross-section `CollisionState` (boundary point + velocity);
* the deterministic minimal-time next-collision map `next?` defined via `Table.DeterministicNext.next?`.

This file intentionally does **not** prove the remaining WS7.3 geometry obligations:
no-spurious-collisions / uniqueness / tangency exclusion on any interesting `Good` set, nor any
semiconjugacy to the WS7.4 symbolic map. It is a definitional scaffold for that work.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set

namespace PaperReadWriteTableCanonical

open Table
open Table.DeterministicNext

/-- Canonical boundary union for the read–write gadget, including the Appendix-consistent rewrite redirecting walls. -/
def boundary : Set V :=
  PaperReadWriteBoundary.rwWallUnionCanonical ∪
    PaperReadWriteBoundary.tildeWallUnionCanonical ∪
    PaperReadWriteBoundary.rwWallRewriteUnionCanonical ∪
    PaperReadWrite.tildeWallRewriteAppendixUnionCanonical

/--
A noncomputable normal selector on the canonical boundary union.

This is *staged*: it uses classical choice to pick a witness wall family for the boundary point and
returns the corresponding (outward) normal. Corner points lying on multiple walls are expected to
be excluded by the eventual WS7.3 `Good` predicate, so no consistency across overlaps is claimed.
-/
noncomputable def normal (q : {p // p ∈ boundary}) : V := by
  classical
  -- Split by wall family.
  rcases q.property with hABC | hD
  · rcases hABC with hAB | hC
    · rcases hAB with hA | hB
      · -- read-only separating wall
        rcases hA with ⟨k, pref, cur, _hd, _hp⟩
        exact PaperReadWrite.rwWallNormal cur
      · -- read-only redirecting wall
        rcases hB with ⟨k, pref, cur, _hd, _hp⟩
        exact PaperReadWrite.rwWallNormal cur
    · -- rewrite separating wall
      rcases hC with ⟨k, pref, cur, _hd, _hp⟩
      exact PaperReadWrite.rwWallRewriteNormal k (pref ++ [cur]) cur
  · -- rewrite redirecting wall (Appendix-consistent)
    rcases hD with ⟨k, pref, cur, _hd, _hp⟩
    exact PaperReadWrite.rwWallRewriteNormal k (pref ++ [cur]) cur

/-- The staged canonical “full gadget” table: inside is `univ`, boundary is the union above. -/
def table : Billiards.Table :=
  { inside := Set.univ
    boundary := boundary
    normal := normal }

@[simp] theorem table_boundary : table.boundary = boundary := rfl
@[simp] theorem table_inside : table.inside = Set.univ := rfl

/-! ## Collision cross-section and deterministic next collision -/

/-- Collision-space state: a boundary point and a velocity. -/
structure CollisionState where
  pos : V
  vel : V
  pos_mem : pos ∈ boundary

def CollisionState.toState (s : CollisionState) : Billiards.State :=
  ⟨s.pos, s.vel⟩

/-- “Good” collision states for deterministic evolution: unique first-hit time from `s.toState`. -/
def Good (s : CollisionState) : Prop :=
  Table.DeterministicNext.Good table (s.toState)

private theorem next?_pos_mem_boundary {s : Billiards.State} {s' : Billiards.State}
    (h : Table.DeterministicNext.next? table s = some s') : s'.pos ∈ boundary := by
  classical
  -- Unfold `next?` and extract the chosen boundary point.
  unfold Table.DeterministicNext.next? at h
  split_ifs at h with hgood
  · -- In the `Good` branch, the output is `⟨q, reflect ...⟩` with `q ∈ boundary`.
    have htFirst :
        Table.DeterministicNext.IsFirstHitTime table s (Classical.choose (ExistsUnique.exists hgood)) :=
      (Classical.choose_spec (ExistsUnique.exists hgood)).1
    have hq : Table.DeterministicNext.hitPoint table s (Classical.choose (ExistsUnique.exists hgood)) ∈ table.boundary :=
      (htFirst.1.2).1
    -- Identify `s'.pos` by `Option.some.inj`.
    have hs' :
        s' =
          ⟨Table.DeterministicNext.hitPoint table s (Classical.choose (ExistsUnique.exists hgood)),
            reflect (table.normal ⟨Table.DeterministicNext.hitPoint table s (Classical.choose (ExistsUnique.exists hgood)), hq⟩) s.vel⟩ := by
      simpa using (Option.some.inj h)
    simpa [table_boundary] using congrArg Billiards.State.pos hs' ▸ hq
  · cases h

/-- Deterministic minimal-time next collision, defined on collision-space states. -/
noncomputable def next? (s : CollisionState) : Option CollisionState := by
  classical
  match h : Table.DeterministicNext.next? table s.toState with
  | none => exact none
  | some s' =>
      exact some ⟨s'.pos, s'.vel, next?_pos_mem_boundary (s := s.toState) (s' := s') h⟩

end PaperReadWriteTableCanonical

end Billiards
end MirandaDynamics
end HeytingLean
