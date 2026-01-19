import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteBoundary
import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteTableReadOnly

/-!
# MirandaDynamics.Billiards: staged two-bounce semantics for the read-only straight gadget

This file extends `PaperReadWriteTableReadOnly` by adding the redirecting walls
`tildeWallUnionCanonical` to the boundary and packaging the **two-bounce** read-only gadget as a
`Billiards.Table` reachability statement:

`entryState e ⟶ hitPoint e ⟶ hitPoint₂ e`

This remains staged: it does not yet prove *trajectory-level* “no spurious collisions” across the
full infinite boundary union, nor does it define a global minimal-time `next?`.
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

namespace ReadOnlyTwoBounceTable

open HeytingLean.MirandaDynamics.Billiards.Table

/-! ## Table with boundary `rwWallUnionCanonical ∪ tildeWallUnionCanonical` -/

noncomputable def boundary : Set V :=
  rwWallUnionCanonical ∪ tildeWallUnionCanonical

noncomputable def table : Billiards.Table :=
  { inside := Set.univ
    boundary := boundary
    normal := fun q =>
      -- Pick a witness from whichever side of the union contains `q.1`.
      if hrw : q.1 ∈ rwWallUnionCanonical then
        let w :
            (Σ k : ℤ, Σ pref : List Bool, Σ cur : Bool,
              PaperReadWriteBoundary.rwDigits k pref cur ∧ q.1 ∈ rwWall k (pref ++ [cur]) cur) :=
          Classical.choose hrw
        rwWallNormal w.2.2.1
      else
        have htilde : q.1 ∈ tildeWallUnionCanonical := by
          rcases q.2 with h | h
          · exact (hrw h).elim
          · exact h
        let w :
            (Σ k : ℤ, Σ pref : List Bool, Σ cur : Bool,
              PaperReadWriteBoundary.rwDigits k pref cur ∧ q.1 ∈ tildeWall k (pref ++ [cur]) cur) :=
          Classical.choose htilde
        rwWallNormal w.2.2.1 }

@[simp] theorem table_inside : table.inside = Set.univ := rfl
@[simp] theorem table_boundary : table.boundary = boundary := rfl

/-! ## Two-bounce derived points/states -/

/-- The explicit second collision point (computed from the first hit and the reflected velocity). -/
def hitPoint₂ (e : Entry) : V :=
  hitPoint e + (2 : ℝ) • hitVel e

def hitState₁ (e : Entry) : Billiards.State :=
  ⟨hitPoint e, hitVel e⟩

def hitState₂ (e : Entry) : Billiards.State :=
  ⟨hitPoint₂ e, reflect (rwWallNormal (cur e)) (hitVel e)⟩

theorem hitPoint₂_x (e : Entry) : x (hitPoint₂ e) = e.x0 + shift (cur e) := by
  -- Expand and use the explicit formula for the reflected velocity.
  have hv : hitVel e = (if cur e then eX else -eX) := by
    simpa [hitVel, entryVel] using (ReadOnlyCollision.reflect_rwWallNormal_eY (cur := cur e))
  cases hcur : cur e <;> simp [hitPoint₂, hitPoint, entryPos, entryVel, hv, hcur, Plane.x, Plane.eX, Plane.eY]

theorem hitPoint₂_y (e : Entry) : y (hitPoint₂ e) = hitTime e := by
  have hv : hitVel e = (if cur e then eX else -eX) := by
    simpa [hitVel, entryVel] using (ReadOnlyCollision.reflect_rwWallNormal_eY (cur := cur e))
  cases hcur : cur e <;> simp [hitPoint₂, hitPoint, hv, hcur, Plane.y, Plane.eX, Plane.eY]

theorem hitPoint₂_mem_tildeWall (e : Entry) :
    hitPoint₂ e ∈ tildeWall e.k (pref e ++ [cur e]) (cur e) := by
  have hx0 : e.x0 ∈ rwBlockInterval e.k (pref e ++ [cur e]) := x0_mem_block_Icc e
  have hv : hitVel e = (if cur e then eX else -eX) := by
    simpa [hitVel, entryVel] using (ReadOnlyCollision.reflect_rwWallNormal_eY (cur := cur e))
  -- Reduce to coordinate arithmetic.
  cases hcur : cur e <;>
    simp [hitPoint₂, hitPoint, hitTime, hv, hcur, tildeWall, shift, rwBlockCenter, hx0,
      Plane.mk, Plane.x, Plane.y, Plane.eX, Plane.eY, entryVel, entryPos, add_assoc, add_left_comm, add_comm] <;>
    constructor <;> linarith

theorem hitPoint₂_mem_boundary (e : Entry) : hitPoint₂ e ∈ table.boundary := by
  refine Or.inr ?_
  refine ⟨e.k, pref e, cur e, ?_, ?_⟩
  · exact ⟨pref_length e⟩
  · simpa [PaperReadWriteBoundary.rwDigits] using hitPoint₂_mem_tildeWall e

/-! ## Two-step reachability -/

theorem entry_Step₁ (e : Entry) : table.Step (entryState e) (hitState₁ e) := by
  -- Reuse the first-step construction from `ReadOnlyWallTable`, upgrading boundary membership.
  refine ⟨hitPoint e, ?_, ?_, rfl, rfl⟩
  · -- `hitPoint` lies on the rw-wall union, hence on the new boundary.
    refine Or.inl ?_
    -- Exhibit the chosen canonical index.
    refine ⟨e.k, pref e, cur e, ?_, ?_⟩
    · exact ⟨pref_length e⟩
    · simpa [PaperReadWriteBoundary.rwDigits] using (hitPoint_mem_rwWall e)
  · -- Flight is the same (inside is `univ`).
    -- The outgoing velocity is by definition `hitVel e`.
    have : reflect (table.normal ⟨hitPoint e, by
        -- show boundary membership again for the normal field
        refine Or.inl ?_
        exact ⟨e.k, pref e, cur e, ⟨pref_length e⟩, by
          simpa [PaperReadWriteBoundary.rwDigits] using hitPoint_mem_rwWall e⟩⟩) (entryVel e) = hitVel e := by
      -- The `normal` picks `rwWallNormal (cur e)` on rw-wall points; compute by uniqueness of the witness.
      -- We avoid unfolding the `Classical.choose` witness by observing that *any* witness has the same `cur`.
      classical
      -- Unfold `table.normal` and simplify using the branch `hrw := True`.
      have hrw : hitPoint e ∈ rwWallUnionCanonical := by
        exact ⟨e.k, pref e, cur e, ⟨pref_length e⟩, by
          simpa [PaperReadWriteBoundary.rwDigits] using hitPoint_mem_rwWall e⟩
      -- Reduce the `if` to the `rw` branch.
      simp [table, boundary, hrw, hitVel, entryVel]
    refine ⟨hitTime e, hitTime_pos e, ?_, ?_⟩
    · simp [entryState, hitState₁, entryPos, entryVel, hitPoint, this, Plane.mk, Plane.eY]
    · simp [table, Billiards.Table.Flight]

theorem hitState₁_Step₂ (e : Entry) : table.Step (hitState₁ e) (hitState₂ e) := by
  refine ⟨hitPoint₂ e, hitPoint₂_mem_boundary e, ?_, rfl, rfl⟩
  -- Flight from `hitPoint` to `hitPoint₂` along the constant-velocity segment.
  refine ⟨(2 : ℝ), by norm_num, ?_, ?_⟩
  · simp [hitPoint₂, hitState₁, smul_add, add_assoc, add_left_comm, add_comm]
  · simp [table, Billiards.Table.Flight]

theorem entry_Reaches_hitState₂ (e : Entry) : table.Reaches (entryState e) (hitState₂ e) := by
  refine Table.Reaches.trans table (Table.Step.reaches (T := table) (entry_Step₁ e)) ?_
  exact Table.Step.reaches (T := table) (hitState₁_Step₂ e)

end ReadOnlyTwoBounceTable

end PaperReadWrite

end Billiards
end MirandaDynamics
end HeytingLean

