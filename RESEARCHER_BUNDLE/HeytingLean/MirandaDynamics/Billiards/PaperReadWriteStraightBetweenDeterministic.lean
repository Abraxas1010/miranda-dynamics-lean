import HeytingLean.MirandaDynamics.Billiards.GeometryDeterministicNext
import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteCollisionAppendixFlight
import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteFlightAvoidanceCanonical
import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteWallsAppendix

/-!
# MirandaDynamics.Billiards: deterministic minimal-time next collision for the straight gadget (Appendix flight line)

This file turns the Appendix-style disjointness lemmas (`flightRayLeft0` / `flightRayRight1`) into
an **actual segment-level first-hit** statement in the `GeometryDeterministicNext` framework.

Scope of this milestone:
* we build a table whose boundary contains the full **canonical union** of separating walls
  `rwWall … cur` for a fixed `cur` branch, with singular endpoints excluded in the same one-sided
  way as the Appendix disjointness lemmas;
* we add a single intended redirecting wall `tildeWallAppendix` and prove that the extremal flight
  segment hits it at time `2` with no earlier boundary hits.

This is a corridor-local deterministic-next building block toward WS7.3.
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
open AppendixStraight

namespace AppendixBetween

/-- Canonical extremal-flight entry: choose a head index `k` and a prefix of length `indexNat k`. -/
structure Entry where
  k : ℤ
  pref : List Bool
  cur : Bool
  hlen : PaperReadWriteBoundary.rwDigits k pref cur

abbrev ds (e : Entry) : List Bool := e.pref ++ [e.cur]

def wallState (e : Entry) : AppendixStraight.State :=
  { k := e.k, ds := ds e, cur := e.cur }

def startPos (e : Entry) : V :=
  AppendixStraight.upperEndpoint (wallState e)

def startVel (e : Entry) : V :=
  AppendixStraight.vel (wallState e)

def startState (e : Entry) : Billiards.State :=
  ⟨startPos e, startVel e⟩

/-! ## Boundary: canonical union of straight walls (one-sided endpoint exclusion) -/

/-- The canonical straight wall union for a fixed `cur`, with the singular endpoint excluded in the
same one-sided manner as the Appendix disjointness lemmas. -/
def rwWallUnionCanonicalNoEndpoint (cur : Bool) : Set V :=
  { p |
      ∃ k : ℤ, ∃ pref : List Bool, PaperReadWriteBoundary.rwDigits k pref cur ∧
        p ∈ rwWall k (pref ++ [cur]) cur ∧
          (if cur then rwBlockLeft k (pref ++ [cur]) < x p
           else x p < rwBlockLeft k (pref ++ [cur]) + rwBlockLen k (pref ++ [cur])) }

/-- Table used for the between-wall flight: all separating walls for this `cur` branch (with
endpoint excluded) plus the full canonical union of Appendix redirecting walls. -/
def table (e : Entry) : Billiards.Table :=
  { inside := Set.univ
    boundary := rwWallUnionCanonicalNoEndpoint e.cur ∪ tildeWallAppendixUnionCanonical
    normal := fun _ => rwWallNormal e.cur }

@[simp] theorem table_inside (e : Entry) : (table e).inside = Set.univ := rfl
@[simp] theorem table_boundary (e : Entry) :
    (table e).boundary = rwWallUnionCanonicalNoEndpoint e.cur ∪ tildeWallAppendixUnionCanonical := rfl

/-! ## The explicit hit at time `2` (intended redirecting wall) -/

def hitPoint₂ (e : Entry) : V :=
  startPos e + (2 : ℝ) • startVel e

theorem hitPoint₂_mem_tildeWallAppendix (e : Entry) : hitPoint₂ e ∈ tildeWallAppendix e.k (ds e) e.cur := by
  classical
  -- Expand the endpoint and velocity definitions.
  cases hcur : e.cur
  · -- `cur=false`: upper endpoint is the left endpoint; velocity is `-(eX+eY)`.
    have hx : x (hitPoint₂ e) = rwBlockLeft e.k (ds e) - 2 := by
      simp [hitPoint₂, startPos, startVel, wallState, AppendixStraight.upperEndpoint, AppendixStraight.vel, hcur,
        Plane.x, Plane.y, Plane.eX, Plane.eY]
    have hy : y (hitPoint₂ e) = rwBlockLen e.k (ds e) / 2 := by
      simp [hitPoint₂, startPos, startVel, wallState, AppendixStraight.upperEndpoint, AppendixStraight.vel, hcur,
        AppendixStraight.endpointY, Plane.x, Plane.y, Plane.eX, Plane.eY]
      ring_nf
    refine ⟨?_, ?_⟩
    · -- x is the left endpoint of the shifted interval.
      have hlen : 0 ≤ rwBlockLen e.k (ds e) := le_of_lt (rwBlockLen_pos e.k (ds e))
      constructor <;> linarith [hx, hlen]
    · -- y-equation.
      have : y (hitPoint₂ e) = rwBlockCenter e.k (ds e) - (x (hitPoint₂ e) - shift false) := by
        simp [hy, hx, rwBlockCenter, shift, hcur]
        ring_nf
      simpa [tildeWallAppendix, hcur, this]
  · -- `cur=true`: upper endpoint is the right endpoint; velocity is `eX-eY`.
    have hx : x (hitPoint₂ e) = (rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e)) + 2 := by
      simp [hitPoint₂, startPos, startVel, wallState, AppendixStraight.upperEndpoint, AppendixStraight.vel, hcur,
        Plane.x, Plane.y, Plane.eX, Plane.eY]
    have hy : y (hitPoint₂ e) = rwBlockLen e.k (ds e) / 2 := by
      simp [hitPoint₂, startPos, startVel, wallState, AppendixStraight.upperEndpoint, AppendixStraight.vel, hcur,
        AppendixStraight.endpointY, Plane.x, Plane.y, Plane.eX, Plane.eY]
      ring_nf
    refine ⟨?_, ?_⟩
    · -- x is the right endpoint of the shifted interval.
      have hlen : 0 ≤ rwBlockLen e.k (ds e) := le_of_lt (rwBlockLen_pos e.k (ds e))
      constructor <;> linarith [hx, hlen]
    · -- y-equation.
      have : y (hitPoint₂ e) = -rwBlockCenter e.k (ds e) + (x (hitPoint₂ e) - shift true) := by
        simp [hy, hx, rwBlockCenter, shift, hcur]
        ring_nf
      simpa [tildeWallAppendix, hcur, this]

theorem hitPoint₂_mem_boundary (e : Entry) : hitPoint₂ e ∈ (table e).boundary := by
  refine Or.inr ?_
  refine ⟨e.k, e.pref, e.cur, e.hlen, ?_⟩
  simpa [ds] using hitPoint₂_mem_tildeWallAppendix e

/-! ## No earlier boundary hits (segment-level) -/

theorem hitPoint_mem_flightRay (e : Entry) (t : ℝ) (ht : 0 ≤ t) :
    (startPos e + t • startVel e) ∈ AppendixStraight.flightRay (wallState e) := by
  have : startPos e + t • startVel e ∈ AppendixStraight.traj (wallState e) := by
    refine ⟨t, ht, rfl⟩
  exact (AppendixStraight.traj_subset_flightRay (wallState e)) this

theorem no_rwWallUnionCanonicalNoEndpoint_hit_before_two (e : Entry) {t : ℝ}
    (ht0 : 0 < t) (ht2 : t < 2) :
    Table.DeterministicNext.hitPoint (table e) (startState e) t ∉ rwWallUnionCanonicalNoEndpoint e.cur := by
  classical
  -- Put the hit point on the relevant Appendix flight ray.
  have hflight :
      Table.DeterministicNext.hitPoint (table e) (startState e) t ∈ AppendixStraight.flightRay (wallState e) := by
    have ht0' : 0 ≤ t := le_of_lt ht0
    simpa [Table.DeterministicNext.hitPoint, startState, startPos, startVel] using hitPoint_mem_flightRay e t ht0'
  -- Unpack a hypothetical boundary membership and contradict disjointness.
  intro hmem
  rcases hmem with ⟨k', pref', hdigits, hpWall, hendpoint⟩
  -- Split by the `cur` branch to use the matching disjointness lemma.
  cases hcur : e.cur
  · -- `cur=false`: use `flightRayLeft0` disjointness against any canonical wall.
    have hpRay :
        Table.DeterministicNext.hitPoint (table e) (startState e) t ∈ flightRayLeft0 e.k (ds e) := by
      simpa [AppendixStraight.flightRay, wallState, ds, hcur] using hflight
    -- Either `k' < k`, `k' = k`, or `k < k'`.
    rcases lt_trichotomy k' e.k with hklt | hkeq | hkgt
    · have hdis :=
        rwWall_false_disjoint_flightRayLeft0_of_lt_canonical
          (k := e.k) (k' := k') hklt (pref := e.pref) (pref' := pref')
          (hL := by simpa [PaperReadWriteBoundary.rwDigits] using e.hlen)
          (hL' := by simpa [PaperReadWriteBoundary.rwDigits] using hdigits)
      exact (Set.disjoint_left.1 hdis) ⟨hpWall, hendpoint⟩ hpRay
    · subst hkeq
      by_cases hpref : pref' = e.pref
      · subst hpref
        -- The flight ray immediately moves strictly left of the wall’s x-domain.
        have hxWall : rwBlockLeft e.k (ds e) ≤ x (Table.DeterministicNext.hitPoint (table e) (startState e) t) := by
          exact hpWall.1.1
        have hxRay : x (Table.DeterministicNext.hitPoint (table e) (startState e) t) ≤ rwBlockLeft e.k (ds e) := by
          exact hpRay.2
        have hxEq : x (Table.DeterministicNext.hitPoint (table e) (startState e) t) = rwBlockLeft e.k (ds e) :=
          le_antisymm hxRay hxWall
        -- But on the ray, `x = left - t` and `t>0`, contradiction.
        have : x (Table.DeterministicNext.hitPoint (table e) (startState e) t) = rwBlockLeft e.k (ds e) - t := by
          simp [Table.DeterministicNext.hitPoint, startState, startPos, startVel, wallState, ds, AppendixStraight.upperEndpoint,
            AppendixStraight.endpointY, AppendixStraight.vel, hcur, Plane.x, Plane.eX, Plane.eY]
        have : t = 0 := by linarith [hxEq, this]
        exact (lt_irrefl (0 : ℝ)) (this ▸ ht0)
      · -- Different canonical block at the same `k`.
        have hlenEq : (pref' ++ [false]).length = (e.pref ++ [false]).length := by
          simp [PaperReadWriteBoundary.rwDigits] at hdigits e.hlen
          simp [List.length_append, hdigits, e.hlen]
        have hdis :=
          rwWall_false_disjoint_flightRayLeft0_of_ne (k := e.k) (ds := e.pref ++ [false]) (ds' := pref' ++ [false])
            hlenEq (by
              intro hEq
              apply hpref
              have := congrArg (fun l => l.take e.pref.length) hEq.symm
              simpa using this)
        exact (Set.disjoint_left.1 hdis) ⟨hpWall, hendpoint⟩ hpRay
    · -- `k < k'`: easy cross-`k` exclusion (wrong side of the head ordering).
      have hdis : Disjoint (rwWall k' (pref' ++ [false]) false) (flightRayLeft0 e.k (ds e)) :=
        rwWall_disjoint_flightRayLeft0_of_k_lt (k := e.k) (k' := k') (ds := ds e) (ds' := pref' ++ [false])
          (cur' := false) hkgt
      exact (Set.disjoint_left.1 (hdis.mono_left (by
        intro p hp
        exact hp.1))) hpWall hpRay
  · -- `cur=true`: symmetric, using `flightRayRight1`.
    have hpRay :
        Table.DeterministicNext.hitPoint (table e) (startState e) t ∈ flightRayRight1 e.k (ds e) := by
      simpa [AppendixStraight.flightRay, wallState, ds, hcur] using hflight
    rcases lt_trichotomy e.k k' with hklt | hkeq | hkgt
    · -- `k < k'`.
      have hdis :=
        rwWall_true_disjoint_flightRayRight1_of_lt_canonical
          (k := e.k) (k' := k') hklt (pref := e.pref) (pref' := pref')
          (hL := by simpa [PaperReadWriteBoundary.rwDigits] using e.hlen)
          (hL' := by simpa [PaperReadWriteBoundary.rwDigits] using hdigits)
      exact (Set.disjoint_left.1 hdis) ⟨hpWall, hendpoint⟩ hpRay
    · subst hkeq
      by_cases hpref : pref' = e.pref
      · subst hpref
        -- The flight ray immediately moves strictly right of the wall’s x-domain.
        have hxWall : x (Table.DeterministicNext.hitPoint (table e) (startState e) t) ≤ rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e) := by
          exact hpWall.1.2
        have hxRay : rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e) ≤ x (Table.DeterministicNext.hitPoint (table e) (startState e) t) := by
          exact hpRay.2
        have hxEq :
            x (Table.DeterministicNext.hitPoint (table e) (startState e) t) = rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e) :=
          le_antisymm hxWall hxRay
        have : x (Table.DeterministicNext.hitPoint (table e) (startState e) t) =
            (rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e)) + t := by
          simp [Table.DeterministicNext.hitPoint, startState, startPos, startVel, wallState, ds, AppendixStraight.upperEndpoint,
            AppendixStraight.endpointY, AppendixStraight.vel, hcur, Plane.x, Plane.eX, Plane.eY]
        have : t = 0 := by linarith [hxEq, this]
        exact (lt_irrefl (0 : ℝ)) (this ▸ ht0)
      · have hlenEq : (pref' ++ [true]).length = (e.pref ++ [true]).length := by
          simp [PaperReadWriteBoundary.rwDigits] at hdigits e.hlen
          simp [List.length_append, hdigits, e.hlen]
        have hdis :=
          rwWall_true_disjoint_flightRayRight1_of_ne (k := e.k) (ds := e.pref ++ [true]) (ds' := pref' ++ [true])
            hlenEq (by
              intro hEq
              apply hpref
              have := congrArg (fun l => l.take e.pref.length) hEq.symm
              simpa using this)
        exact (Set.disjoint_left.1 hdis) ⟨hpWall, hendpoint⟩ hpRay
    · -- `k' < k`: easy cross-`k` exclusion (wrong side).
      have hdis : Disjoint (rwWall k' (pref' ++ [true]) true) (flightRayRight1 e.k (ds e)) :=
        rwWall_disjoint_flightRayRight1_of_k_gt (k := e.k) (k' := k') (ds := ds e) (ds' := pref' ++ [true])
          (cur' := true) hkgt
      exact (Set.disjoint_left.1 (hdis.mono_left (by
        intro p hp
        exact hp.1))) hpWall hpRay

theorem no_boundary_hit_before_two (e : Entry) {t : ℝ} (ht0 : 0 < t) (ht2 : t < 2) :
    Table.DeterministicNext.hitPoint (table e) (startState e) t ∉ (table e).boundary := by
  intro hmem
  rcases hmem with hmem | hmem
  · -- Exclude hits on the straight-wall union via disjointness.
    exact no_rwWallUnionCanonicalNoEndpoint_hit_before_two e ht0 ht2 hmem
  · -- Any hit on the canonical redirecting-wall union forces `t = 2` (the intended wall),
    -- hence contradicts `t < 2`.
    classical
    -- Unpack the canonical union witness.
    rcases hmem with ⟨k', pref', cur', hdigits', hp'⟩
    -- First, show the redirecting-wall branch `cur'` matches the trajectory branch `e.cur`
    -- by comparing `x`-ranges: `cur'=true` walls live at `x ≥ 2`, `cur'=false` at `x ≤ 0`.
    have hcur' : cur' = e.cur := by
      have hxTraj :
          x (Table.DeterministicNext.hitPoint (table e) (startState e) t) =
            (if e.cur then (rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e)) + t else rwBlockLeft e.k (ds e) - t) := by
        simp [Table.DeterministicNext.hitPoint, startState, startPos, startVel, wallState, ds,
          AppendixStraight.upperEndpoint, AppendixStraight.endpointY, AppendixStraight.vel,
          Plane.x, Plane.eX, Plane.eY]
      -- The `x`-membership for `tildeWallAppendix` gives a coarse lower/upper bound.
      have hxWall :
          x (Table.DeterministicNext.hitPoint (table e) (startState e) t) ∈
            Set.Icc (rwBlockLeft k' (pref' ++ [cur']) + shift cur')
              (rwBlockLeft k' (pref' ++ [cur']) + shift cur' + rwBlockLen k' (pref' ++ [cur'])) := by
        exact (mem_tildeWallAppendix_iff (k := k') (ds := pref' ++ [cur']) (cur := cur')
          (p := Table.DeterministicNext.hitPoint (table e) (startState e) t)).1 hp' |>.1
      have hx01 : rwBlockLeft k' (pref' ++ [cur']) + rwBlockLen k' (pref' ++ [cur']) ≤ (1 : ℝ) := by
        -- `rwBlockInterval` lies in `headInterval k' ⊆ [0,1]`.
        have hxHead :
            (rwBlockLeft k' (pref' ++ [cur']) + rwBlockLen k' (pref' ++ [cur'])) ∈ headInterval k' := by
          -- right endpoint is `tau k' (cantorLeft + cantorWidth)`.
          have hx01' : (cantorLeft (pref' ++ [cur']) + cantorWidth (pref' ++ [cur'])) ∈ Set.Icc (0 : ℝ) 1 := by
            refine ⟨?_, cantorLeft_add_width_le_one (pref' ++ [cur'])⟩
            have h0 : 0 ≤ cantorLeft (pref' ++ [cur']) := cantorLeft_nonneg (pref' ++ [cur'])
            have h1 : 0 ≤ cantorWidth (pref' ++ [cur']) := by
              unfold cantorWidth
              have : 0 < (3 : ℝ) ^ (pref' ++ [cur']).length := by positivity
              exact le_of_lt (inv_pos.2 this)
            linarith
          have ht :
              tau k' (cantorLeft (pref' ++ [cur']) + cantorWidth (pref' ++ [cur'])) =
                rwBlockLeft k' (pref' ++ [cur']) + rwBlockLen k' (pref' ++ [cur']) := by
            simp [rwBlockLeft, rwBlockLen, tau_eq_affine, cantorWidth, mul_add, add_assoc, add_left_comm, add_comm]
          simpa [headInterval] using (ht ▸ tau_mem_headInterval (k := k') (x := cantorLeft (pref' ++ [cur']) + cantorWidth (pref' ++ [cur'])) hx01')
        exact le_trans hxHead.2 (headRight_le_one k')
      have hx_lt_two :
          x (Table.DeterministicNext.hitPoint (table e) (startState e) t) < (2 : ℝ) := by
        -- The extremal-flight `x` coordinate stays within `[-2,3]` and, on `t<2`, is never ≥ 2
        -- in the `cur=false` branch.
        cases hcur : e.cur
        · -- `cur=false`: `x = left - t ≤ left ≤ 1`.
          have hleft_le_one : rwBlockLeft e.k (ds e) ≤ (1 : ℝ) := by
            have hLmem : rwBlockLeft e.k (ds e) ∈ headInterval e.k := by
              have hx01e : cantorLeft (ds e) ∈ Set.Icc (0 : ℝ) 1 := ⟨cantorLeft_nonneg (ds e), cantorLeft_le_one (ds e)⟩
              simpa [rwBlockLeft] using (tau_mem_headInterval (k := e.k) (x := cantorLeft (ds e)) hx01e)
            exact le_trans hLmem.2 (headRight_le_one e.k)
          have : x (Table.DeterministicNext.hitPoint (table e) (startState e) t) ≤ (1 : ℝ) := by
            simpa [hxTraj, hcur] using sub_le_iff_le_add.2 (le_trans hleft_le_one (by linarith))
          linarith
        · -- `cur=true`: `x = right + t`, and on `t<2` it is < 3.
          have : x (Table.DeterministicNext.hitPoint (table e) (startState e) t) < (3 : ℝ) := by
            have hright_le_one : rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e) ≤ (1 : ℝ) := by
              have hrmem : (rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e)) ∈ headInterval e.k := by
                -- right endpoint in headInterval
                have hx01e : (cantorLeft (ds e) + cantorWidth (ds e)) ∈ Set.Icc (0 : ℝ) 1 := by
                  refine ⟨?_, cantorLeft_add_width_le_one (ds e)⟩
                  have h0 : 0 ≤ cantorLeft (ds e) := cantorLeft_nonneg (ds e)
                  have h1 : 0 ≤ cantorWidth (ds e) := by
                    unfold cantorWidth
                    have : 0 < (3 : ℝ) ^ (ds e).length := by positivity
                    exact le_of_lt (inv_pos.2 this)
                  linarith
                have ht' :
                    tau e.k (cantorLeft (ds e) + cantorWidth (ds e)) =
                      rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e) := by
                  simp [rwBlockLeft, rwBlockLen, tau_eq_affine, cantorWidth, mul_add, add_assoc, add_left_comm, add_comm]
                simpa [headInterval] using (ht' ▸ tau_mem_headInterval (k := e.k) (x := cantorLeft (ds e) + cantorWidth (ds e)) hx01e)
              exact le_trans hrmem.2 (headRight_le_one e.k)
            have : x (Table.DeterministicNext.hitPoint (table e) (startState e) t) ≤ (1 : ℝ) + t := by
              simpa [hxTraj, hcur, add_assoc, add_left_comm, add_comm] using add_le_add_right hright_le_one t
            have : x (Table.DeterministicNext.hitPoint (table e) (startState e) t) < (1 : ℝ) + (2 : ℝ) := by
              exact lt_of_le_of_lt this (add_lt_add_left ht2 _)
            simpa using this
          -- In the `cur=true` branch, the `cur'=false` tilde walls live at `x ≤ 0`, so `cur'` must be true.
          -- So we only need `x < 2` when `cur' = true`, which follows from `x ≥ 2` for such walls.
          -- We'll use a direct `cur'` split below.
          linarith
      -- Now conclude by splitting on `cur'`.
      cases hcur'e : cur' with
      · -- `cur'=false`: tilde walls satisfy `x ≤ 0` (since `shift=false = -2` and `rwBlockLeft+len ≤ 1`).
        have hx_le_zero :
            x (Table.DeterministicNext.hitPoint (table e) (startState e) t) ≤ (0 : ℝ) := by
          have hxU : x (Table.DeterministicNext.hitPoint (table e) (startState e) t) ≤
              rwBlockLeft k' (pref' ++ [false]) + shift false + rwBlockLen k' (pref' ++ [false]) := hxWall.2
          have : rwBlockLeft k' (pref' ++ [false]) + shift false + rwBlockLen k' (pref' ++ [false]) ≤ 0 := by
            -- `rwBlockLeft+rwBlockLen ≤ 1` and `shift false = -2`.
            have hx01' : rwBlockLeft k' (pref' ++ [false]) + rwBlockLen k' (pref' ++ [false]) ≤ (1 : ℝ) := by
              simpa using (hx01 (cur' := false))
            simp [shift] at this
            nlinarith [hx01']
          exact le_trans hxU this
        -- On the `cur=true` flight, `x` is strictly positive; on `cur=false` it is < 2, so either way we can conclude `e.cur=false`.
        cases hcur : e.cur
        · exact (by simp [hcur_e] at hcur; simpa [hcur])
        · have hxPos : (0 : ℝ) < x (Table.DeterministicNext.hitPoint (table e) (startState e) t) := by
            -- `x = right + t` and `t>0` with `right ≥ 0`.
            have hright_nonneg : 0 ≤ rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e) := by
              have hrmem : (rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e)) ∈ headInterval e.k := by
                have hx01e : (cantorLeft (ds e) + cantorWidth (ds e)) ∈ Set.Icc (0 : ℝ) 1 := by
                  refine ⟨?_, cantorLeft_add_width_le_one (ds e)⟩
                  have h0 : 0 ≤ cantorLeft (ds e) := cantorLeft_nonneg (ds e)
                  have h1 : 0 ≤ cantorWidth (ds e) := by
                    unfold cantorWidth
                    have : 0 < (3 : ℝ) ^ (ds e).length := by positivity
                    exact le_of_lt (inv_pos.2 this)
                  linarith
                have ht' :
                    tau e.k (cantorLeft (ds e) + cantorWidth (ds e)) =
                      rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e) := by
                  simp [rwBlockLeft, rwBlockLen, tau_eq_affine, cantorWidth, mul_add, add_assoc, add_left_comm, add_comm]
                simpa [headInterval] using (ht' ▸ tau_mem_headInterval (k := e.k) (x := cantorLeft (ds e) + cantorWidth (ds e)) hx01e)
              exact le_trans (headLeft_nonneg e.k) hrmem.1
            have : 0 < rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e) + t := by
              exact add_pos_of_nonneg_of_pos hright_nonneg ht0
            simpa [hxTraj, hcur] using this
          exact (lt_irrefl (0 : ℝ)) (lt_of_le_of_lt hx_le_zero hxPos)
      · -- `cur'=true`: tilde walls satisfy `x ≥ 2` (since `shift=true=2` and `rwBlockLeft ≥ 0`).
        have hx_ge_two :
            (2 : ℝ) ≤ x (Table.DeterministicNext.hitPoint (table e) (startState e) t) := by
          have hxL : rwBlockLeft k' (pref' ++ [true]) + shift true ≤ x (Table.DeterministicNext.hitPoint (table e) (startState e) t) := hxWall.1
          have hleft_nonneg : 0 ≤ rwBlockLeft k' (pref' ++ [true]) := by
            have hLmem : rwBlockLeft k' (pref' ++ [true]) ∈ headInterval k' := by
              have hx01' : cantorLeft (pref' ++ [true]) ∈ Set.Icc (0 : ℝ) 1 :=
                ⟨cantorLeft_nonneg (pref' ++ [true]), cantorLeft_le_one (pref' ++ [true])⟩
              simpa [rwBlockLeft] using (tau_mem_headInterval (k := k') (x := cantorLeft (pref' ++ [true])) hx01')
            exact le_trans (headLeft_nonneg k') hLmem.1
          simp [shift] at hxL
          nlinarith [hxL, hleft_nonneg]
        have : x (Table.DeterministicNext.hitPoint (table e) (startState e) t) < (2 : ℝ) := hx_lt_two
        exact (not_lt_of_ge hx_ge_two) this
    subst hcur'
    -- Now `cur' = e.cur`: solve the wall equation for `t`, then contradict `t < 2`.
    have : t = 2 := by
      -- Use the `y` equation from membership in `tildeWallAppendix` and compute `x,y` along the trajectory.
      have hy :
          y (Table.DeterministicNext.hitPoint (table e) (startState e) t) =
            (if e.cur then (-rwBlockCenter k' (pref' ++ [e.cur]) + (x (Table.DeterministicNext.hitPoint (table e) (startState e) t) - shift e.cur))
             else (rwBlockCenter k' (pref' ++ [e.cur]) - (x (Table.DeterministicNext.hitPoint (table e) (startState e) t) - shift e.cur))) := by
        simpa [mem_tildeWallAppendix_iff] using
          (mem_tildeWallAppendix_iff (k := k') (ds := pref' ++ [e.cur]) (cur := e.cur)
            (p := Table.DeterministicNext.hitPoint (table e) (startState e) t)).1 hp' |>.2
      have hx :
          x (Table.DeterministicNext.hitPoint (table e) (startState e) t) =
            (if e.cur then (rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e)) + t else rwBlockLeft e.k (ds e) - t) := by
        simp [Table.DeterministicNext.hitPoint, startState, startPos, startVel, wallState, ds, AppendixStraight.upperEndpoint,
          AppendixStraight.endpointY, AppendixStraight.vel, Plane.x, Plane.eX, Plane.eY]
      have hyTraj :
          y (Table.DeterministicNext.hitPoint (table e) (startState e) t) =
            (2 : ℝ) + (rwBlockLen e.k (ds e)) / 2 - t := by
        simp [Table.DeterministicNext.hitPoint, startState, startPos, startVel, wallState, ds, AppendixStraight.upperEndpoint,
          AppendixStraight.endpointY, AppendixStraight.vel, Plane.y, Plane.eX, Plane.eY]
        ring_nf
      -- Solve `hyTraj = hy` for `t`; the only solution is `t=2` when the wall index matches.
      -- We reduce to equality of wall data using the `x`-interval constraint at `t<2`.
      -- First, extract the `x`-interval membership and translate it back to `rwBlockInterval`.
      have hxWall' :
          (x (Table.DeterministicNext.hitPoint (table e) (startState e) t) - shift e.cur) ∈
            rwBlockInterval k' (pref' ++ [e.cur]) := by
        rcases (mem_tildeWallAppendix_iff (k := k') (ds := pref' ++ [e.cur]) (cur := e.cur)
          (p := Table.DeterministicNext.hitPoint (table e) (startState e) t)).1 hp' |>.1 with ⟨hxL, hxU⟩
        constructor <;> linarith
      -- Also, show that `x - shift` lies in the *intended* block interval (near the endpoint for `t<2`).
      have hxIntended :
          (x (Table.DeterministicNext.hitPoint (table e) (startState e) t) - shift e.cur) ∈
            rwBlockInterval e.k (ds e) := by
        -- Rewrite `x - shift` using the explicit trajectory, then bound it into the intended block interval
        -- using `t<2` and the fact the segment stays within one block-width of the endpoint.
        cases hcur : e.cur <;>
          simp [hx, hcur, shift, rwBlockInterval, rwBlockLeft, rwBlockLen] at *
      -- From the two `rwBlockInterval` memberships, infer equality of `k` and `ds` (canonical indexing).
      have hk : k' = e.k := by
        by_contra hkne
        have hdis : Disjoint (rwBlockInterval e.k (ds e)) (rwBlockInterval k' (pref' ++ [e.cur])) :=
          rwBlockInterval_disjoint_of_k_ne (k := e.k) (k' := k') hkne (ds := ds e) (ds' := pref' ++ [e.cur])
        exact (Set.disjoint_left.1 hdis) hxIntended hxWall'
      subst hk
      have hds : pref' ++ [e.cur] = ds e := by
        -- Both prefixes have the canonical length `indexNat e.k`.
        have hL : e.pref.length = indexNat e.k := e.hlen
        have hL' : pref'.length = indexNat e.k := by
          simpa [PaperReadWriteBoundary.rwDigits] using hdigits'
        -- Apply the `rwDigits`-based interval uniqueness lemma.
        exact rwBlockInterval_eq_of_mem_of_rwDigits (k := e.k) (pref := e.pref) (pref' := pref') (cur := e.cur)
          (cur' := e.cur) (x := x (Table.DeterministicNext.hitPoint (table e) (startState e) t) - shift e.cur)
          hL hL' hxIntended hxWall'
      -- With `k'=k` and `ds'=ds`, solve `hyTraj = hy`.
      subst hds
      cases e.cur <;> simp [hyTraj, hx, shift, rwBlockCenter] at hy <;> nlinarith [hy]
    exact (not_lt_of_eq this) ht2

theorem start_Good_firstHit (e : Entry) :
    Table.DeterministicNext.Good (table e) (startState e) := by
  classical
  refine ExistsUnique.intro (2 : ℝ) ?exist ?uniq
  · -- `2` is a first-hit time.
    refine And.intro ?hit ?noEarlier
    · refine ⟨by norm_num, ?_⟩
      refine ⟨hitPoint₂_mem_boundary e, ?_⟩
      simp [Table.DeterministicNext.IsHitTime, Table.DeterministicNext.hitPoint, table, startState, hitPoint₂,
        Billiards.Table.Flight]
    · intro t ht0 htlt
      exact no_boundary_hit_before_two e ht0 (lt_of_lt_of_le htlt (by norm_num))
  · intro t htFirst
    -- If `t > 2`, then `2` would be an earlier boundary hit; so `t ≤ 2`.
    have htpos : 0 < t := htFirst.1.1.1
    have htle : t ≤ 2 := by
      by_contra hgt
      have : (2 : ℝ) < t := lt_of_not_ge hgt
      have h2mem : Table.DeterministicNext.hitPoint (table e) (startState e) 2 ∈ (table e).boundary := by
        simpa [Table.DeterministicNext.hitPoint, startState, hitPoint₂] using hitPoint₂_mem_boundary e
      exact (htFirst.2 2 (by norm_num) this) h2mem
    -- If `t < 2`, it contradicts the no-earlier-hit lemma at time `t`.
    have hneq : ¬t < 2 := by
      intro hlt
      have hmem : Table.DeterministicNext.hitPoint (table e) (startState e) t ∈ (table e).boundary := (htFirst.1.1.2).1
      exact no_boundary_hit_before_two e htpos hlt hmem
    exact le_antisymm htle (le_of_not_gt hneq)

theorem start_isFirstHitTime_two (e : Entry) :
    Table.DeterministicNext.IsFirstHitTime (table e) (startState e) (2 : ℝ) := by
  refine And.intro ?hit ?noEarlier
  · refine And.intro (by norm_num) ?_
    refine And.intro ?mem ?seg
    · simpa [Table.DeterministicNext.hitPoint, startState, hitPoint₂] using hitPoint₂_mem_boundary e
    · -- `inside = univ`, so the segment condition is trivial.
      simp [table]
  · intro t ht0 htlt
    have ht2 : t < 2 := by simpa using htlt
    exact no_boundary_hit_before_two e ht0 ht2

theorem next?_eq_some (e : Entry) :
    Table.DeterministicNext.next? (table e) (startState e) =
      some ⟨hitPoint₂ e, reflect (rwWallNormal e.cur) (startVel e)⟩ := by
  classical
  have hgood : Table.DeterministicNext.Good (table e) (startState e) := start_Good_firstHit e
  -- Unfold `next?` and pin down the chosen first-hit time using uniqueness.
  unfold Table.DeterministicNext.next?
  split_ifs with h
  · -- Identify the chosen time as `2`.
    let t : ℝ := Classical.choose (ExistsUnique.exists h)
    have htFirst : Table.DeterministicNext.IsFirstHitTime (table e) (startState e) t :=
      (Classical.choose_spec (ExistsUnique.exists h)).1
    have htEq : t = (2 : ℝ) := by
      exact ExistsUnique.unique h htFirst (start_isFirstHitTime_two e)
    subst htEq
    -- Normalize the hit point and the constant normal field.
    simp [Table.DeterministicNext.hitPoint, startState, hitPoint₂, table, startPos, startVel]
  · exact (hgood h).elim

/-! ## The symmetric return step (reflect at `tildeWallAppendix` and come back to the upper endpoint) -/

def afterState (e : Entry) : Billiards.State :=
  ⟨hitPoint₂ e, reflect (rwWallNormal e.cur) (startVel e)⟩

@[simp] theorem afterState_pos (e : Entry) : (afterState e).pos = hitPoint₂ e := rfl
@[simp] theorem afterState_vel (e : Entry) : (afterState e).vel = reflect (rwWallNormal e.cur) (startVel e) := rfl

theorem reflect_startVel_eq_neg (e : Entry) :
    reflect (rwWallNormal e.cur) (startVel e) = -startVel e := by
  cases hcur : e.cur
  · -- `cur=false`: `startVel = -(eX+eY)` is (a scalar multiple of) the normal.
    simp [startVel, wallState, AppendixStraight.vel, hcur, rwWallNormal, reflect_normal_eq_neg, sub_eq_add_neg]
  · -- `cur=true`: `startVel = eX-eY` is exactly the normal.
    simp [startVel, wallState, AppendixStraight.vel, hcur, rwWallNormal, reflect_normal_eq_neg, sub_eq_add_neg]

theorem after_hitPoint_eq (e : Entry) (t : ℝ) :
    Table.DeterministicNext.hitPoint (table e) (afterState e) t = startPos e + (2 - t) • startVel e := by
  -- Use the explicit hitpoint and the fact the post-hit velocity is `-startVel`.
  simp [Table.DeterministicNext.hitPoint, afterState, hitPoint₂, reflect_startVel_eq_neg, sub_smul, add_assoc, add_left_comm,
    add_comm]

theorem startPos_mem_rwWallUnionCanonicalNoEndpoint (e : Entry) :
    startPos e ∈ rwWallUnionCanonicalNoEndpoint e.cur := by
  classical
  refine ⟨e.k, e.pref, e.hlen, ?_, ?_⟩
  · -- boundary membership in the underlying wall segment.
    simpa [startPos, wallState] using AppendixStraight.upperEndpoint_mem_rwWall (s := wallState e)
  · -- one-sided endpoint exclusion (the endpoint is strict interior on the appropriate side).
    have hlenPos : 0 < rwBlockLen e.k (ds e) := rwBlockLen_pos e.k (ds e)
    cases hcur : e.cur
    · -- left endpoint
      have hx : x (startPos e) = rwBlockLeft e.k (ds e) := by
        simp [startPos, wallState, AppendixStraight.upperEndpoint, hcur, Plane.x, Plane.mk]
      simp [rwWallUnionCanonicalNoEndpoint, hcur, hx]
      nlinarith [hlenPos]
    · -- right endpoint
      have hx : x (startPos e) = rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e) := by
        simp [startPos, wallState, AppendixStraight.upperEndpoint, hcur, Plane.x, Plane.mk]
      simp [rwWallUnionCanonicalNoEndpoint, hcur, hx]
      nlinarith [hlenPos]

theorem after_isFirstHitTime_two (e : Entry) :
    Table.DeterministicNext.IsFirstHitTime (table e) (afterState e) (2 : ℝ) := by
  refine And.intro ?hit ?noEarlier
  · refine And.intro (by norm_num) ?_
    refine And.intro ?mem ?seg
    · -- At time `2` we return to `startPos`, which is in the straight-wall union.
      have : Table.DeterministicNext.hitPoint (table e) (afterState e) (2 : ℝ) = startPos e := by
        simp [Table.DeterministicNext.hitPoint, afterState, hitPoint₂, reflect_startVel_eq_neg]
      refine ?_
      -- membership in the rw-wall part of the union
      have hmem : startPos e ∈ (table e).boundary := by
        refine Or.inl (startPos_mem_rwWallUnionCanonicalNoEndpoint e)
      simpa [this] using hmem
    · -- `inside = univ`, so segment condition is trivial.
      simp [table]
  · intro t ht0 htlt
    -- Convert an early boundary hit on the return segment into an early boundary hit on the forward segment.
    have ht2 : t < 2 := by simpa using htlt
    have ht'pos : 0 < (2 - t) := sub_pos.2 ht2
    have ht'lt : (2 - t) < 2 := by linarith
    -- The points coincide: return at `t` equals forward at `2-t`.
    have hpt :
        Table.DeterministicNext.hitPoint (table e) (afterState e) t =
          Table.DeterministicNext.hitPoint (table e) (startState e) (2 - t) := by
      simp [Table.DeterministicNext.hitPoint, startState, afterState, hitPoint₂, reflect_startVel_eq_neg, sub_smul,
        add_assoc, add_left_comm, add_comm]
    -- Apply the forward no-early-hit lemma.
    intro hboundary
    have : Table.DeterministicNext.hitPoint (table e) (startState e) (2 - t) ∈ (table e).boundary := by
      simpa [hpt] using hboundary
    exact no_boundary_hit_before_two e ht'pos ht'lt this

theorem after_Good_firstHit (e : Entry) :
    Table.DeterministicNext.Good (table e) (afterState e) := by
  classical
  refine ExistsUnique.intro (2 : ℝ) ?exist ?uniq
  · exact after_isFirstHitTime_two e
  · intro t htFirst
    have htpos : 0 < t := htFirst.1.1.1
    have htle : t ≤ 2 := by
      by_contra hgt
      have : (2 : ℝ) < t := lt_of_not_ge hgt
      have h2mem : Table.DeterministicNext.hitPoint (table e) (afterState e) 2 ∈ (table e).boundary :=
        (after_isFirstHitTime_two e).1.2.1
      exact (htFirst.2 2 (by norm_num) this) h2mem
    have hneq : ¬t < 2 := by
      intro hlt
      have hmem : Table.DeterministicNext.hitPoint (table e) (afterState e) t ∈ (table e).boundary :=
        (htFirst.1.1.2).1
      -- `t<2` contradicts `after_isFirstHitTime_two`.
      exact (after_isFirstHitTime_two e).2 t htpos hlt hmem
    exact le_antisymm htle (le_of_not_gt hneq)

theorem after_next?_eq_some (e : Entry) :
    Table.DeterministicNext.next? (table e) (afterState e) =
      some ⟨startPos e, startVel e⟩ := by
  classical
  have hgood : Table.DeterministicNext.Good (table e) (afterState e) := after_Good_firstHit e
  unfold Table.DeterministicNext.next?
  split_ifs with h
  · let t : ℝ := Classical.choose (ExistsUnique.exists h)
    have htFirst : Table.DeterministicNext.IsFirstHitTime (table e) (afterState e) t :=
      (Classical.choose_spec (ExistsUnique.exists h)).1
    have htEq : t = (2 : ℝ) := by
      exact ExistsUnique.unique h htFirst (after_isFirstHitTime_two e)
    subst htEq
    -- At time `2` we return to `startPos`; the reflected velocity is `startVel` by involutivity.
    simp [Table.DeterministicNext.hitPoint, afterState, hitPoint₂, reflect_startVel_eq_neg, table, startState, startPos,
      startVel]
  · exact (hgood h).elim

theorem next?_eq_some_afterState (e : Entry) :
    Table.DeterministicNext.next? (table e) (startState e) = some (afterState e) := by
  simpa [afterState] using next?_eq_some e

theorem next?_afterState_eq_some_startState (e : Entry) :
    Table.DeterministicNext.next? (table e) (afterState e) = some (startState e) := by
  simpa [startState] using after_next?_eq_some e

end AppendixBetween

end PaperReadWrite

end Billiards
end MirandaDynamics
end HeytingLean
