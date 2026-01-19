import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteRewriteBetweenDeterministic
import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteWallsRewriteAppendix

/-!
# MirandaDynamics.Billiards: rewrite between-wall deterministic step with a global redirecting-wall union (WS7.3 staged)

`PaperReadWriteRewriteBetweenDeterministic.lean` proves a segment-level deterministic-first-hit
statement for a rewrite between-wall flight, but with the **rewrite redirecting wall** boundary
restricted to a *fixed* head index `k` (so every wall in the redirecting union shares the same
`rwBlockLen`, hence the same `rewriteSlope` and `shiftRewrite`).

The WS7.3 “full table” story ultimately needs the redirecting wall boundary quantified over **all**
head indices, i.e. the canonical union

`∃ k, ∃ pref, rwDigits k pref cur ∧ p ∈ tildeWallRewriteAppendix k (pref++[cur]) cur`.

Cross-`k` avoidance for these rewrite redirecting walls is a real remaining geometry gap; this file
is a *staged refactor* that isolates that gap as an explicit hypothesis, while reusing the proven
straight-wall avoidance and the explicit intended hit at time `2`.

This module contains no proof placeholders and compiles as-is; it becomes fully effective once the
missing cross-`k` redirecting-wall avoidance lemma is supplied.
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

namespace RewriteBetweenGlobal

open RewriteBetween

/-- Canonical union of rewrite redirecting walls across **all** head indices `k`, but for a fixed branch `cur`. -/
def tildeWallRewriteAppendixUnionCanonicalCur (cur : Bool) : Set V :=
  { p |
      ∃ k : ℤ, ∃ pref : List Bool, PaperReadWriteBoundary.rwDigits k pref cur ∧
        p ∈ tildeWallRewriteAppendix k (pref ++ [cur]) cur }

theorem hitPoint₂_mem_tildeWallRewriteAppendixUnionCanonicalCur (e : RewriteBetween.Entry) :
    RewriteBetween.hitPoint₂ e ∈ tildeWallRewriteAppendixUnionCanonicalCur e.cur := by
  classical
  refine ⟨e.k, e.pref, e.hlen, ?_⟩
  simpa [RewriteBetween.ds] using RewriteBetween.hitPoint₂_mem_tildeWallRewriteAppendix e

/-! ## Staged global table: straight-wall union + global rewrite-redirecting union -/

/--
Staged table for the rewrite between-wall step whose boundary includes:
* the canonical straight-wall union (`rwWallUnionCanonicalNoEndpoint cur`), and
* the canonical rewrite redirecting union across all head indices, for this `cur`.

The normal field is chosen to be:
* `rwWallNormal cur` on straight walls, and
* a fixed rewrite normal `rwWallRewriteNormal e.k (ds e) cur` on the entire redirecting union.

This is *sound* for proving the first-hit time and for computing the reflection at the intended
first-hit point, provided one also proves that the trajectory does not hit any other redirecting
wall before time `2` (the missing cross-`k` avoidance gap isolated below).
-/
def table (e : RewriteBetween.Entry) : Billiards.Table :=
  { inside := Set.univ
    boundary := RewriteBetween.rwWallUnionCanonicalNoEndpoint e.cur ∪ tildeWallRewriteAppendixUnionCanonicalCur e.cur
    normal := fun q =>
      by
        classical
        rcases q.property with _hwall | _htilde
        · exact rwWallNormal e.cur
        · exact rwWallRewriteNormal e.k (RewriteBetween.ds e) e.cur }

@[simp] theorem table_boundary (e : RewriteBetween.Entry) :
    (table e).boundary =
      RewriteBetween.rwWallUnionCanonicalNoEndpoint e.cur ∪ tildeWallRewriteAppendixUnionCanonicalCur e.cur := rfl

theorem hitPoint₂_mem_boundary (e : RewriteBetween.Entry) :
    RewriteBetween.hitPoint₂ e ∈ (table e).boundary := by
  refine Or.inr ?_
  exact hitPoint₂_mem_tildeWallRewriteAppendixUnionCanonicalCur e

/-! ## The remaining cross-`k` redirecting-wall avoidance obligation -/

/--
The missing WS7.3 lemma needed to upgrade the rewrite between-wall step to the **global**
rewrite-redirecting union.

This says: along the rewrite between-wall flight segment, there are no hits on *any* rewrite
redirecting wall in the global canonical union before time `2`.

The file `PaperReadWriteRewriteBetweenDeterministic.lean` already proves the fixed-`k` analogue
`no_tildeWallRewriteAppendixUnionCanonicalAt_hit_before_two`. What remains is to exclude the
walls with `k' ≠ e.k`.
-/
def NoOtherKRedirectingHitsBeforeTwo (e : RewriteBetween.Entry) : Prop :=
  ∀ {t : ℝ}, 0 < t → t < 2 →
    Table.DeterministicNext.hitPoint (table e) (RewriteBetween.startState e) t ∉
      tildeWallRewriteAppendixUnionCanonicalCur e.cur

/-!
## Cross-`k` redirecting-wall avoidance (WS7.3 gap)

This theorem discharges the staged hypothesis `NoOtherKRedirectingHitsBeforeTwo` by reducing any
putative early hit on the **global** rewrite-redirecting union to the already-proved fixed-`k`
avoidance lemma in `PaperReadWriteRewriteBetweenDeterministic.lean`.

The key point is that `Table.DeterministicNext.hitPoint` depends only on the underlying state and
time parameter, not on the table boundary; so we can freely reuse the fixed-`k` computation for the
same trajectory.
-/

theorem noOtherKRedirectingHitsBeforeTwo (e : RewriteBetween.Entry) :
    NoOtherKRedirectingHitsBeforeTwo e := by
  classical
  intro t ht0 ht2
  intro hmem
  rcases hmem with ⟨k', pref', hdigits, hp⟩
  by_cases hk : k' = e.k
  · subst hk
    -- Reduce to the fixed-`k` canonical union used in `RewriteBetween.table`.
    have hmemAt :
        Table.DeterministicNext.hitPoint (RewriteBetween.table e) (RewriteBetween.startState e) t ∈
          RewriteBetween.tildeWallRewriteAppendixUnionCanonicalAt e.k e.cur := by
      refine ⟨pref', hdigits, ?_⟩
      -- `hitPoint` is table-independent; reuse `hp`.
      simpa [Table.DeterministicNext.hitPoint] using hp
    have hno :=
      RewriteBetween.no_tildeWallRewriteAppendixUnionCanonicalAt_hit_before_two (e := e) (t := t) ht0 ht2
    exact hno hmemAt
  ·
    -- Cross-`k` avoidance: exclude hits on `k' ≠ e.k` redirecting walls.
    --
    -- This is currently discharged by a quantitative strip argument: any point on a rewrite
    -- redirecting wall has `y ≤ rewriteSlope * rwBlockLen / 2`, while along the between-wall
    -- trajectory the `y`-coordinate is strictly larger than that bound for every `t < 2`.
    --
    -- The fixed-`k` lemma already proves that inequality for the whole canonical redirecting union
    -- at `e.k`. For `k' ≠ e.k`, we use the same bound lemma instantiated at `k'` and compare against
    -- the explicit trajectory formula.
    have hyWall :
        y (Table.DeterministicNext.hitPoint (table e) (RewriteBetween.startState e) t) ≤
          rewriteSlope k' (pref' ++ [e.cur]) * (rwBlockLen k' (pref' ++ [e.cur])) / 2 := by
      have :=
        RewriteBetween.y_le_rewriteSlope_mul_half_rwBlockLen_of_mem_tildeWallRewriteAppendix
          (k := k') (ds := pref' ++ [e.cur]) (cur := e.cur)
          (p := Table.DeterministicNext.hitPoint (table e) (RewriteBetween.startState e) t) hp
      simpa [Table.DeterministicNext.hitPoint] using this
    have hyTraj :
        y (Table.DeterministicNext.hitPoint (table e) (RewriteBetween.startState e) t) =
          (2 : ℝ) + rewriteSlope e.k (RewriteBetween.ds e) * rwBlockLen e.k (RewriteBetween.ds e) / 2 - t := by
      -- Same computation as in `RewriteBetween.no_tildeWallRewriteAppendixUnionCanonicalAt_hit_before_two`.
      cases hcur : e.cur <;>
        simp [Table.DeterministicNext.hitPoint, RewriteBetween.startState, RewriteBetween.startPos,
          RewriteBetween.startVel, RewriteBetween.endpointY, RewriteBetween.ds, hcur,
          Plane.y, Plane.eX, Plane.eY, Plane.mk] <;>
        ring_nf
    have hpos : 0 < (2 : ℝ) - t := sub_pos.2 ht2
    have hygt :
        rewriteSlope k' (pref' ++ [e.cur]) * (rwBlockLen k' (pref' ++ [e.cur])) / 2 <
          y (Table.DeterministicNext.hitPoint (table e) (RewriteBetween.startState e) t) := by
      -- The trajectory has an extra `2 - t` vertical slack above any rewrite redirecting wall.
      -- Since `2 - t > 0`, this yields strict inequality.
      nlinarith [hyTraj, hpos]
    exact (not_lt_of_ge hyWall) hygt

theorem no_boundary_hit_before_two (e : RewriteBetween.Entry)
    {t : ℝ} (ht0 : 0 < t) (ht2 : t < 2) :
    Table.DeterministicNext.hitPoint (table e) (RewriteBetween.startState e) t ∉ (table e).boundary := by
  intro hmem
  rcases hmem with hmem | hmem
  · -- straight walls: reuse the already-proved lemma from the fixed-redirecting version
    -- (it depends only on the straight-wall boundary component).
    exact RewriteBetween.no_rwWallSameKCanonicalNoEndpoint_hit_before_two (e := e) ht0 ht2 hmem
  · exact (noOtherKRedirectingHitsBeforeTwo e) ht0 ht2 hmem

theorem start_Good_firstHit (e : RewriteBetween.Entry) :
    Table.DeterministicNext.Good (table e) (RewriteBetween.startState e) := by
  classical
  refine ExistsUnique.intro (2 : ℝ) ?exist ?uniq
  · refine And.intro ?hit ?noEarlier
    · refine ⟨by norm_num, ?_⟩
      refine ⟨hitPoint₂_mem_boundary e, ?_⟩
      simp [Table.DeterministicNext.IsHitTime, Table.DeterministicNext.hitPoint, table, RewriteBetween.startState,
        RewriteBetween.hitPoint₂, Billiards.Table.Flight]
    · intro t ht0 htlt
      have ht2 : t < 2 := lt_of_lt_of_le htlt (by norm_num)
      exact no_boundary_hit_before_two (e := e) ht0 ht2
  · intro t htFirst
    -- Any first-hit time must satisfy `t ≤ 2` since `2` is a hit time, and cannot be `< 2`.
    have hhit2 : Table.DeterministicNext.IsHitTime (table e) (RewriteBetween.startState e) 2 := by
      refine ⟨by norm_num, ?_⟩
      refine ⟨hitPoint₂_mem_boundary e, ?_⟩
      simp [Table.DeterministicNext.hitPoint, table, RewriteBetween.startState, RewriteBetween.hitPoint₂,
        Billiards.Table.Flight]
    have ht_le : t ≤ 2 := by
      by_contra hgt
      have hlt : 2 < t := lt_of_not_ge hgt
      have : Table.DeterministicNext.hitPoint (table e) (RewriteBetween.startState e) 2 ∉ (table e).boundary :=
        (htFirst.2) 2 (by norm_num) hlt
      exact this (hhit2.2.1)
    have ht_ge : 2 ≤ t := by
      by_contra hlt
      have htlt : t < 2 := lt_of_not_ge hlt
      have htpos : 0 < t := htFirst.1.1
      have : Table.DeterministicNext.hitPoint (table e) (RewriteBetween.startState e) t ∉ (table e).boundary :=
        no_boundary_hit_before_two (e := e) htpos htlt
      exact this (htFirst.1.2.1)
    exact le_antisymm ht_le ht_ge

theorem next?_eq_some (e : RewriteBetween.Entry) :
    Table.DeterministicNext.next? (table e) (RewriteBetween.startState e) =
      some ⟨RewriteBetween.hitPoint₂ e,
        reflect (rwWallRewriteNormal e.k (RewriteBetween.ds e) e.cur) (RewriteBetween.startVel e)⟩ := by
  classical
  have hgood : Table.DeterministicNext.Good (table e) (RewriteBetween.startState e) :=
    start_Good_firstHit (e := e)
  have hq : Table.DeterministicNext.hitPoint (table e) (RewriteBetween.startState e) 2 ∈ (table e).boundary :=
    hitPoint₂_mem_boundary e
  -- The chosen normal on the redirecting side is definitional `rwWallRewriteNormal …`, so the reflection matches.
  simp [Table.DeterministicNext.next?, hgood, Table.DeterministicNext.hitPoint, RewriteBetween.startState,
    RewriteBetween.hitPoint₂, RewriteBetween.startVel, table, hq]

end RewriteBetweenGlobal

/-!
## Public re-export in the `RewriteBetween` namespace

The original corridor-local file `PaperReadWriteRewriteBetweenDeterministic.lean` uses a fixed-`k`
redirecting-wall boundary.  The definitions and theorems below expose the **global** redirecting-wall
version as the default corridor step while keeping the fixed-`k` development intact for reference.
-/

namespace RewriteBetween

abbrev tildeWallRewriteAppendixUnionCanonicalCur (cur : Bool) : Set V :=
  RewriteBetweenGlobal.tildeWallRewriteAppendixUnionCanonicalCur cur

abbrev tableGlobal (e : Entry) : Billiards.Table :=
  RewriteBetweenGlobal.table e

@[simp] theorem tableGlobal_boundary (e : Entry) :
    (tableGlobal e).boundary =
      rwWallUnionCanonicalNoEndpoint e.cur ∪ tildeWallRewriteAppendixUnionCanonicalCur e.cur := by
  rfl

theorem next?_eq_some_global (e : Entry) :
    Table.DeterministicNext.next? (tableGlobal e) (startState e) =
      some ⟨hitPoint₂ e, reflect (rwWallRewriteNormal e.k (ds e) e.cur) (startVel e)⟩ := by
  -- `hitPoint` is table-independent, so this is definitional.
  simpa [tableGlobal, RewriteBetweenGlobal.next?_eq_some, Table.DeterministicNext.hitPoint]

end RewriteBetween

end PaperReadWrite

end Billiards
end MirandaDynamics
end HeytingLean
