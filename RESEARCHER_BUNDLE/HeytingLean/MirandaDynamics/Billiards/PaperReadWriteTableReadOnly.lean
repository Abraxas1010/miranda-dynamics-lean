import HeytingLean.MirandaDynamics.Billiards.Geometry
import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteCorridorReadOnly

/-!
# MirandaDynamics.Billiards: a staged geometric table for the read-only straight wall union

This file packages the **read-only** canonical straight walls `rwWallUnionCanonical` as a
`Geometry.Table` and proves a first “global minimal-time next collision” theorem for a restricted
cross-section:

* entry states are vertical rays starting at `y=0` over a point `x0` strictly inside some canonical
  block at a fixed head-index `k` (see `PaperReadWrite.ReadOnlyCorridor.Entry`);
* the next collision is uniquely determined and equals the explicit `rwWall` hit (as in
  `PaperReadWriteCollision`).

This is a mechanizable stepping stone toward the full WS7.3 geometry gap:
it handles an **infinite boundary union** (over all `k` and digit-prefixes), but it does not yet
include redirecting corridors, rewrite walls, or parabolic shift walls.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set
open Plane

namespace PaperReadWrite

open ReadOnlyCorridor

/-! ## A `Geometry.Table` instance with boundary `rwWallUnionCanonical` -/

namespace ReadOnlyWallTable

open HeytingLean.MirandaDynamics.Billiards.Table

noncomputable def table : Billiards.Table :=
  { inside := Set.univ
    boundary := rwWallUnionCanonical
    normal := fun q =>
      -- Choose an index witnessing that `q` lies on a canonical wall, and use that wall’s normal.
      let w : (Σ k : ℤ, Σ pref : List Bool, Σ cur : Bool, PaperReadWriteBoundary.rwDigits k pref cur ∧
          (q.1 ∈ rwWall k (pref ++ [cur]) cur)) :=
        Classical.choose q.2
      rwWallNormal w.2.2.1 }

@[simp] theorem table_inside : table.inside = Set.univ := rfl
@[simp] theorem table_boundary : table.boundary = rwWallUnionCanonical := rfl

/-! ## Entry semantics and unique next collision -/

def entryPos (e : Entry) : V := Plane.mk e.x0 0
def entryVel (_e : Entry) : V := eY

def entryState (e : Entry) : Billiards.State := ⟨entryPos e, entryVel e⟩

/-- The (explicit) next-hit time for the chosen canonical block. -/
noncomputable def hitTime (e : Entry) : ℝ :=
  if cur e then e.x0 + 2 - rwBlockCenter e.k (pref e ++ [cur e])
  else 2 + rwBlockCenter e.k (pref e ++ [cur e]) - e.x0

/-- The (explicit) next-hit point on the intended `rwWall`. -/
def hitPoint (e : Entry) : V :=
  Plane.mk e.x0 (hitTime e)

/-- The outgoing velocity after reflecting off the intended wall. -/
def hitVel (e : Entry) : V :=
  reflect (rwWallNormal (cur e)) (entryVel e)

theorem hitTime_pos (e : Entry) : 0 < hitTime e := by
  -- `x0 ∈ (left, left+len)` implies the hit height is in `(2-len/2, 2+len/2)`, hence positive.
  have hx : e.x0 ∈ Set.Ioo (rwBlockLeft e.k (pref e ++ [cur e]))
      (rwBlockLeft e.k (pref e ++ [cur e]) + rwBlockLen e.k (pref e ++ [cur e])) :=
    x0_mem_block_Ioo e
  have hlenpos : 0 < rwBlockLen e.k (pref e ++ [cur e]) :=
    rwBlockLen_pos e.k (pref e ++ [cur e])
  have hcenter : rwBlockCenter e.k (pref e ++ [cur e]) =
      rwBlockLeft e.k (pref e ++ [cur e]) + rwBlockLen e.k (pref e ++ [cur e]) / 2 := by
    simp [rwBlockCenter]
  cases hcur : cur e <;> simp [hitTime, hcur, hcenter] <;> nlinarith [hx.1, hx.2, hlenpos]

theorem hitPoint_mem_rwWall (e : Entry) : hitPoint e ∈ rwWall e.k (pref e ++ [cur e]) (cur e) := by
  have hxIcc : e.x0 ∈ rwBlockInterval e.k (pref e ++ [cur e]) := x0_mem_block_Icc e
  cases hcur : cur e <;> simp [hitPoint, hitTime, hcur, rwWall, hxIcc, Plane.mk, Plane.x, Plane.y, rwBlockCenter]

theorem hitPoint_mem_boundary (e : Entry) : hitPoint e ∈ table.boundary := by
  -- Exhibit the chosen canonical index.
  refine ⟨e.k, pref e, cur e, ?_, ?_⟩
  · exact ⟨pref_length e⟩
  · simpa [table_boundary] using hitPoint_mem_rwWall e

theorem entry_Flight_to_hitPoint (e : Entry) :
    table.Flight (entryPos e) (hitPoint e) (entryVel e) := by
  refine ⟨hitTime e, hitTime_pos e, ?_, ?_⟩
  · -- point equation
    simp [entryPos, entryVel, hitPoint, hitTime, Plane.mk, Plane.eY, Plane.x, Plane.y, add_assoc, add_left_comm,
      add_comm, smul_add]
  · -- segment is inside ∪ boundary (inside is `univ`)
    simp [table, Billiards.Table.Flight]

theorem entry_Step_to_hitPoint (e : Entry) :
    table.Step (entryState e) ⟨hitPoint e, hitVel e⟩ := by
  refine ⟨hitPoint e, hitPoint_mem_boundary e, ?_, rfl, rfl⟩
  refine ⟨hitTime e, hitTime_pos e, rfl, ?_⟩
  simp [table, Billiards.Table.Flight]

/-- **Uniqueness** of the boundary point hit by the entry vertical ray: any `rwWallUnionCanonical`
collision along the ray must be the intended one. -/
theorem entry_hitPoint_unique (e : Entry) {q : V} {t : ℝ}
    (ht : 0 < t) (hqRay : q = entryPos e + t • entryVel e) (hqB : q ∈ table.boundary) :
    q = hitPoint e ∧ t = hitTime e := by
  -- Expand `q` coordinates from the ray equation.
  have hxq : x q = e.x0 := by
    subst hqRay
    simp [entryPos, entryVel, Plane.mk, Plane.eY, Plane.x]
  have hyq : y q = t := by
    subst hqRay
    simp [entryPos, entryVel, Plane.mk, Plane.eY, Plane.y]
  -- Unpack boundary membership into an `rwWall` membership.
  rcases hqB with ⟨k', pref', cur', hk', hqWall⟩
  have hx0' : e.x0 ∈ rwBlockInterval k' (pref' ++ [cur']) := by
    -- `x q` belongs to the wall interval, and `x q = x0`.
    simpa [hxq] using hqWall.1
  -- Show the chosen block matches the witness block (uniqueness of canonical block at fixed `k`).
  have hbc : (pref' , cur') = block e := by
    -- First show `k' = k` by disjoint head intervals.
    have hxHead : e.x0 ∈ headInterval e.k := rwBlockInterval_subset_headInterval (k := e.k) (ds := pref e ++ [cur e])
      (x0_mem_block_Icc e)
    have hxHead' : e.x0 ∈ headInterval k' := rwBlockInterval_subset_headInterval (k := k') (ds := pref' ++ [cur'])
      hx0'
    have hkEq : k' = e.k := by
      by_contra hkne
      have hdis : Disjoint (headInterval e.k) (headInterval k') :=
        headInterval_disjoint (k := e.k) (k' := k') (by exact ne_comm.1 hkne)
      exact (Set.disjoint_left.1 hdis) hxHead hxHead'
    subst hkEq
    -- Now apply `block_unique` at this `k`.
    have : (pref', cur') = block e := by
      exact block_unique e (bc := (pref', cur')) ⟨by simpa [PaperReadWriteBoundary.rwDigits] using hk', hx0'⟩
    simpa using this
  -- With matching block, compute the hit point and time from the wall equation.
  have hcurEq : cur' = cur e := congrArg Prod.snd hbc
  have hprefEq : pref' = pref e := congrArg Prod.fst hbc
  subst hcurEq
  subst hprefEq
  -- Now `q` lies on the intended wall, so its `y` coordinate matches the explicit formula.
  have hyWall : y q =
      (2 : ℝ) +
        (if cur e then (-rwBlockCenter e.k (pref e ++ [cur e]) + x q)
         else (rwBlockCenter e.k (pref e ++ [cur e]) - x q)) := by
    simpa [table_boundary] using hqWall.2
  have htEq : t = hitTime e := by
    cases hcur : cur e <;>
      simp [hitTime, hcur, hxq] at hyWall <;> nlinarith [hyq, hyWall]
  -- Conclude `q` matches the explicit hit point.
  refine ⟨?_, htEq⟩
  ext i <;> cases i using Fin.cases <;> simp [hitPoint, Plane.mk, Plane.x, Plane.y, hxq, hyq, htEq]

/-- Decode the underlying Cantor coordinate `x ∈ [0,1]` from the chosen block and read off the
head digit `cur` (this is the symbolic content used by `paperFctrl?`). -/
theorem entry_decode_digit (e : Entry) :
    ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧ tau e.k x = e.x0 ∧ cantorDigitAt? (indexNat e.k) x = some (cur e) := by
  -- Use the image description of `rwBlockInterval` to pick a preimage under `tau`.
  have hx0 : e.x0 ∈ rwBlockInterval e.k (pref e ++ [cur e]) := x0_mem_block_Icc e
  have hxImg : e.x0 ∈ (tau e.k) '' cantorCylinderInterval (pref e ++ [cur e]) := by
    simpa [rwBlockInterval_eq_image_tau (k := e.k) (ds := pref e ++ [cur e])] using hx0
  rcases hxImg with ⟨x, hxCylInt, rfl⟩
  have hx01 : x ∈ Set.Icc (0 : ℝ) 1 := cantorCylinderInterval_subset_Icc (pref e ++ [cur e]) hxCylInt
  -- Convert interval membership to cylinder-set membership and then to the digit block.
  have hxCyl : x ∈ cantorCylinder (pref e ++ [cur e]) := by
    exact (mem_cantorCylinder_iff_mem_interval (ds := pref e ++ [cur e]) (x := x)).2 hxCylInt
  have hxDigit : x ∈ cantorDigitBlock (indexNat e.k) (cur e) := by
    refine ⟨pref e, pref_length e, ?_⟩
    simpa using hxCyl
  have hread : cantorDigitAt? (indexNat e.k) x = some (cur e) :=
    cantorDigitAt?_eq_some_of_mem_cantorDigitBlock (n := indexNat e.k) (cur := cur e) (x := x) hxDigit
  exact ⟨x, hx01, rfl, hread⟩

end ReadOnlyWallTable

end PaperReadWrite

end Billiards
end MirandaDynamics
end HeytingLean
