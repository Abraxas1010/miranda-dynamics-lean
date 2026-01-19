import HeytingLean.MirandaDynamics.Billiards.GeometryDeterministicNext
import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteTableReadOnly

/-!
# MirandaDynamics.Billiards: deterministic `next?` on the read-only entry cross-section

This file instantiates `Table.DeterministicNext.next?` for the staged read-only wall-union table
on the restricted entry cross-section of `PaperReadWriteTableReadOnly`.

It is a small but important bridge:
`entry_hitPoint_unique` (a global uniqueness statement over an infinite boundary union) implies
existence + uniqueness of a *first-hit time*, hence a definable deterministic `next?` on that
cross-section.

This still does not construct the full paper billiard table nor prove corridor-level “no spurious
collisions” for between-wall flights.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set
open Plane

namespace PaperReadWrite

open ReadOnlyCorridor
open ReadOnlyWallTable

namespace ReadOnlyWallTable

open HeytingLean.MirandaDynamics.Billiards.Table
open Table.DeterministicNext

theorem entry_Good_firstHit (e : Entry) :
    DeterministicNext.Good table (entryState e) := by
  classical
  -- Use the explicit `hitTime e` and the uniqueness theorem for boundary hits along the entry ray.
  refine ExistsUnique.intro (hitTime e) ?exist ?uniq
  · -- Show `hitTime e` is a first-hit time.
    refine And.intro ?hit ?noEarlier
    · -- `IsHitTime`
      refine ⟨hitTime_pos e, ?_⟩
      refine ⟨hitPoint_mem_boundary e, ?_⟩
      -- segment is in `inside ∪ boundary` since `inside = univ`
      simp [DeterministicNext.IsHitTime, DeterministicNext.hitPoint, entryState, table, Billiards.Table.Flight,
        entryPos, entryVel, hitPoint, hitTime]
    · intro t' ht' ht'lt
      -- If there were an earlier boundary hit, it would contradict `entry_hitPoint_unique`.
      intro hmem
      have huniq :=
        entry_hitPoint_unique (e := e) (q := hitPoint (entryState e) t') (t := t') ht'
          (by simp [DeterministicNext.hitPoint, entryState, entryPos, entryVel]) hmem
      exact (not_lt_of_eq huniq.2) ht'lt
  · -- Uniqueness of the first-hit time.
    intro t htFirst
    -- Any boundary hit time forces the same hit point/time by `entry_hitPoint_unique`.
    have htpos : 0 < t := htFirst.1.1
    have hqB : hitPoint (entryState e) t ∈ table.boundary := (htFirst.1.2).1
    have huniq := entry_hitPoint_unique (e := e) (q := hitPoint (entryState e) t) (t := t)
      htpos (by
        simp [DeterministicNext.hitPoint, entryState, entryPos, entryVel]) hqB
    exact huniq.2

end ReadOnlyWallTable

end PaperReadWrite

end Billiards
end MirandaDynamics
end HeytingLean
