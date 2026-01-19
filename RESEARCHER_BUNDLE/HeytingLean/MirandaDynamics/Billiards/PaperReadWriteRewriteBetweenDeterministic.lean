import HeytingLean.MirandaDynamics.Billiards.GeometryDeterministicNext
import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteCollisionRewrite
import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteFlightAvoidanceRewriteReduction
import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteFlightAvoidanceCanonical
import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteWallsRewriteAppendix

/-!
# MirandaDynamics.Billiards: deterministic minimal-time next collision for the rewrite between-wall flight (WS7.3)

This file packages a deterministic “between-wall flight” step for the Appendix’s
symbol-change (rewrite) configuration.

Compared with `PaperReadWriteStraightBetweenDeterministic`, the central new ingredient is the
paper’s reduction: rewrite trajectories remain in a half-space **below** the read-only extremal
flight line, so collision avoidance follows from the already-developed endpoint-separation
inequalities (both same-`k` and cross-`k`).
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

namespace RewriteBetween

/-- Canonical between-wall entry for a fixed head index `k`. -/
structure Entry where
  k : ℤ
  pref : List Bool
  cur : Bool
  hlen : PaperReadWriteBoundary.rwDigits k pref cur

abbrev ds (e : Entry) : List Bool := e.pref ++ [e.cur]

/-! ## Start state: upper endpoint of a rewrite wall and a “steeper” downward flight vector -/

noncomputable def endpointY (e : Entry) : ℝ :=
  (2 : ℝ) + (rewriteSlope e.k (ds e)) * (rwBlockLen e.k (ds e)) / 2

def startPos (e : Entry) : V :=
  if e.cur then
    Plane.mk (rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e)) (endpointY e)
  else
    Plane.mk (rwBlockLeft e.k (ds e)) (endpointY e)

def startVel (e : Entry) : V :=
  ((shiftRewrite e.k (ds e) e.cur) / 2) • eX + (-1 : ℝ) • eY

def startState (e : Entry) : Billiards.State :=
  ⟨startPos e, startVel e⟩

/-! ## Boundary: canonical straight-wall union plus the intended rewrite redirecting wall -/

/-- The canonical straight wall union for a fixed `cur`, with the singular endpoint excluded in the
same one-sided manner as the Appendix disjointness lemmas. -/
def rwWallUnionCanonicalNoEndpoint (cur : Bool) : Set V :=
  { p |
      ∃ k : ℤ, ∃ pref : List Bool, PaperReadWriteBoundary.rwDigits k pref cur ∧
        p ∈ rwWall k (pref ++ [cur]) cur ∧
          (if cur then rwBlockLeft k (pref ++ [cur]) < x p
           else x p < rwBlockLeft k (pref ++ [cur]) + rwBlockLen k (pref ++ [cur])) }

/-!
### Rewrite redirecting walls (canonical union, fixed head index)

For the between-wall step at a fixed head index `k`, the Appendix’s redirecting walls are indexed by
the **same** `k` and `cur` but vary the prefix `pref`. This gives a canonical union in which every
wall has the same block length and therefore the same perturbed-slope parameter and normal.
-/

/-- Canonical union of rewrite redirecting walls at a fixed head index `k` and branch `cur`. -/
def tildeWallRewriteAppendixUnionCanonicalAt (k : ℤ) (cur : Bool) : Set V :=
  { p |
      ∃ pref : List Bool,
        PaperReadWriteBoundary.rwDigits k pref cur ∧ p ∈ tildeWallRewriteAppendix k (pref ++ [cur]) cur }

def table (e : Entry) : Billiards.Table :=
  { inside := Set.univ
    boundary := rwWallUnionCanonicalNoEndpoint e.cur ∪ tildeWallRewriteAppendixUnionCanonicalAt e.k e.cur
    normal := fun q =>
      by
        classical
        rcases q.property with _hwall | _htilde
        · exact rwWallNormal e.cur
        · -- All redirecting walls in the fixed-`k` canonical union share the same `rwBlockLen`,
          -- hence the same `rewriteSlope` and the same normal.
          exact rwWallRewriteNormal e.k (ds e) e.cur }

@[simp] theorem table_boundary (e : Entry) :
    (table e).boundary =
      rwWallUnionCanonicalNoEndpoint e.cur ∪ tildeWallRewriteAppendixUnionCanonicalAt e.k e.cur := rfl

/-! ## Explicit intended hit at time `2` -/

def hitPoint₂ (e : Entry) : V :=
  startPos e + (2 : ℝ) • startVel e

theorem hitPoint₂_mem_tildeWallRewriteAppendix (e : Entry) :
    hitPoint₂ e ∈ tildeWallRewriteAppendix e.k (ds e) e.cur := by
  classical
  -- Unfold and compute coordinates at `t=2`.
  cases hcur : e.cur
  · -- `cur=false`: upper endpoint at `x=left`.
    have hx : x (hitPoint₂ e) = rwBlockLeft e.k (ds e) + shiftRewrite e.k (ds e) false := by
      simp [hitPoint₂, startPos, startVel, endpointY, hcur, Plane.x, Plane.eX, Plane.eY, Plane.mk]
      ring_nf
    have hy : y (hitPoint₂ e) = rewriteSlope e.k (ds e) * (rwBlockLen e.k (ds e)) / 2 := by
      simp [hitPoint₂, startPos, startVel, endpointY, hcur, Plane.y, Plane.eX, Plane.eY, Plane.mk]
      ring_nf
    refine ⟨?_, ?_⟩
    · -- `x` is the left endpoint of the shifted interval.
      have hlen : 0 ≤ rwBlockLen e.k (ds e) := le_of_lt (rwBlockLen_pos e.k (ds e))
      constructor <;> linarith [hx, hlen]
    · -- Wall equation.
      have : x (hitPoint₂ e) - shiftRewrite e.k (ds e) false = rwBlockLeft e.k (ds e) := by
        linarith [hx]
      have hcenter : rwBlockCenter e.k (ds e) - (x (hitPoint₂ e) - shiftRewrite e.k (ds e) false) =
          (rwBlockLen e.k (ds e)) / 2 := by
        simp [rwBlockCenter, this]
      simpa [tildeWallRewriteAppendix, hcur, hy, hcenter]
  · -- `cur=true`: upper endpoint at `x=right`.
    have hx : x (hitPoint₂ e) =
        (rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e)) + shiftRewrite e.k (ds e) true := by
      simp [hitPoint₂, startPos, startVel, endpointY, hcur, Plane.x, Plane.eX, Plane.eY, Plane.mk]
      ring_nf
    have hy : y (hitPoint₂ e) = rewriteSlope e.k (ds e) * (rwBlockLen e.k (ds e)) / 2 := by
      simp [hitPoint₂, startPos, startVel, endpointY, hcur, Plane.y, Plane.eX, Plane.eY, Plane.mk]
      ring_nf
    refine ⟨?_, ?_⟩
    · have hlen : 0 ≤ rwBlockLen e.k (ds e) := le_of_lt (rwBlockLen_pos e.k (ds e))
      constructor <;> linarith [hx, hlen]
    · have : x (hitPoint₂ e) - shiftRewrite e.k (ds e) true = rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e) := by
        linarith [hx]
      have hcenter :
          -rwBlockCenter e.k (ds e) + (x (hitPoint₂ e) - shiftRewrite e.k (ds e) true) =
            (rwBlockLen e.k (ds e)) / 2 := by
        simp [rwBlockCenter, this]
      simpa [tildeWallRewriteAppendix, hcur, hy, hcenter, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm]

theorem hitPoint₂_mem_boundary (e : Entry) : hitPoint₂ e ∈ (table e).boundary := by
  refine Or.inr ?_
  refine ⟨e.pref, e.hlen, ?_⟩
  simpa [ds] using hitPoint₂_mem_tildeWallRewriteAppendix e

/-! ## Rewrite trajectory comparison: stay below the read-only extremal flight line -/

private theorem rewriteSlope_lt_one (k : ℤ) (ds : List Bool) : rewriteSlope k ds < 1 := by
  have hlen : 0 < rwBlockLen k ds := rwBlockLen_pos k ds
  have hden : (1 : ℝ) < 1 + rwBlockLen k ds := by linarith
  simpa [rewriteSlope] using (one_div_lt_one (by linarith) |>.2 hden)

/-- Produce the cross-`k` endpoint separation inequality used in the Appendix, given a strict order
of head indices. (This mirrors the case split in `PaperReadWriteFlightAvoidanceCrossK`.) -/
private theorem endpointSepCross_of_lt (k k' : ℤ) (hk : k' < k) (ds ds' : List Bool)
    (hds : 0 < ds.length) (hds' : 0 < ds'.length) :
    PaperReadWriteFlightAvoidanceCrossK.endpointSepCross k ds k' ds' := by
  classical
  -- Split by sign of `k` and `k'` and reuse the quantitative lemmas from the cross-`k` file.
  cases k with
  | ofNat n =>
    cases k' with
    | ofNat m =>
      have hmn : m < n := by
        have : (Int.ofNat m : ℤ) < Int.ofNat n := by simpa using hk
        exact (Int.ofNat_lt).1 this
      exact PaperReadWriteFlightAvoidanceCrossK.endpointSepCross_ofNat_of_lt (m := m) (n := n) hmn ds ds' hds hds'
    | negSucc m =>
      exact PaperReadWriteFlightAvoidanceCrossK.endpointSepCross_ofNat_negSucc (n := n) (m := m) ds ds' hds hds'
  | negSucc n =>
    cases k' with
    | ofNat m =>
      -- Impossible: a nonnegative index is never `<` a negative one.
      have hcontra : ¬ (Int.ofNat m : ℤ) < Int.negSucc n := by
        exact not_lt_of_ge (le_trans (le_of_lt (Int.negSucc_lt_zero n)) (Int.ofNat_nonneg m))
      exact (hcontra (by simpa using hk)).elim
    | negSucc m =>
      -- Convert `negSucc m < negSucc n` to `n < m` and reuse the lemma (roles swapped).
      have hnm : n < m := by
        have : (Int.negSucc m : ℤ) < Int.negSucc n := by simpa using hk
        -- Rewrite both sides as negated `ofNat` and flip the inequality.
        have hm : (Int.negSucc m : ℤ) = -((m + 1 : ℕ) : ℤ) := by simp [Int.negSucc_eq]
        have hn : (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) := by simp [Int.negSucc_eq]
        have : -((m + 1 : ℕ) : ℤ) < -((n + 1 : ℕ) : ℤ) := by simpa [hm, hn] using this
        have : ((n + 1 : ℕ) : ℤ) < ((m + 1 : ℕ) : ℤ) := (Int.neg_lt_neg_iff).1 this
        have : n + 1 < m + 1 := (Int.ofNat_lt).1 this
        exact Nat.lt_of_add_lt_add_right this
      exact PaperReadWriteFlightAvoidanceCrossK.endpointSepCross_negSucc_of_lt (m := n) (n := m) hnm ds ds' hds hds'

theorem hitPoint_mem_belowFlightLine (e : Entry) {t : ℝ} (ht : 0 ≤ t) :
    Table.DeterministicNext.hitPoint (table e) (startState e) t ∈
      (if e.cur then belowFlightLineRight1 e.k (ds e) else belowFlightLineLeft0 e.k (ds e)) := by
  classical
  -- Compute `y±x` along the rewrite trajectory and compare to the read-only extremal constant at `t=0`.
  cases hcur : e.cur
  · -- `cur=false`: show `y - x ≤ 2 + len/2 - left`.
    have hm1 : rewriteSlope e.k (ds e) < 1 := rewriteSlope_lt_one e.k (ds e)
    have hx : x (Table.DeterministicNext.hitPoint (table e) (startState e) t) =
        rwBlockLeft e.k (ds e) + (shiftRewrite e.k (ds e) false) / 2 * t := by
      simp [Table.DeterministicNext.hitPoint, startState, startPos, startVel, endpointY, hcur,
        Plane.x, Plane.eX, Plane.eY, Plane.mk, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm]
    have hy : y (Table.DeterministicNext.hitPoint (table e) (startState e) t) =
        (2 : ℝ) + rewriteSlope e.k (ds e) * rwBlockLen e.k (ds e) / 2 - t := by
      simp [Table.DeterministicNext.hitPoint, startState, startPos, startVel, endpointY, hcur,
        Plane.y, Plane.eX, Plane.eY, Plane.mk]
      ring_nf
    -- At `t=0`, `y-x = 2 + m*len/2 - left ≤ 2 + len/2 - left`.
    have h0 :
        (2 : ℝ) + rewriteSlope e.k (ds e) * rwBlockLen e.k (ds e) / 2 - rwBlockLeft e.k (ds e) ≤
          (2 : ℝ) + rwBlockLen e.k (ds e) / 2 - rwBlockLeft e.k (ds e) := by
      have hlen0 : 0 ≤ rwBlockLen e.k (ds e) / 2 := by
        have : 0 ≤ rwBlockLen e.k (ds e) := le_of_lt (rwBlockLen_pos e.k (ds e))
        nlinarith
      have : rewriteSlope e.k (ds e) * (rwBlockLen e.k (ds e) / 2) ≤ 1 * (rwBlockLen e.k (ds e) / 2) := by
        exact mul_le_mul_of_nonneg_right (le_of_lt hm1) hlen0
      nlinarith [this]
    -- Along the trajectory, `y - x` decreases by a nonnegative amount, so the bound persists.
    have :
        y (Table.DeterministicNext.hitPoint (table e) (startState e) t) -
            x (Table.DeterministicNext.hitPoint (table e) (startState e) t) ≤
          (2 : ℝ) + rwBlockLen e.k (ds e) / 2 - rwBlockLeft e.k (ds e) := by
      -- Use the explicit coordinate forms and `t ≥ 0`.
      -- The term involving `shiftRewrite` only makes `y-x` smaller, so `nlinarith` can close.
      simp [belowFlightLineLeft0, hx, hy]
      nlinarith [h0, ht]
    simpa [hcur] using this
  · -- `cur=true`: show `y + x ≤ 2 + len/2 + right`.
    have hm1 : rewriteSlope e.k (ds e) < 1 := rewriteSlope_lt_one e.k (ds e)
    have hx : x (Table.DeterministicNext.hitPoint (table e) (startState e) t) =
        (rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e)) + (shiftRewrite e.k (ds e) true) / 2 * t := by
      simp [Table.DeterministicNext.hitPoint, startState, startPos, startVel, endpointY, hcur,
        Plane.x, Plane.eX, Plane.eY, Plane.mk, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm]
    have hy : y (Table.DeterministicNext.hitPoint (table e) (startState e) t) =
        (2 : ℝ) + rewriteSlope e.k (ds e) * rwBlockLen e.k (ds e) / 2 - t := by
      simp [Table.DeterministicNext.hitPoint, startState, startPos, startVel, endpointY, hcur,
        Plane.y, Plane.eX, Plane.eY, Plane.mk]
      ring_nf
    have h0 :
        (2 : ℝ) + rewriteSlope e.k (ds e) * rwBlockLen e.k (ds e) / 2 +
            (rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e)) ≤
          (2 : ℝ) + rwBlockLen e.k (ds e) / 2 + (rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e)) := by
      have hlen0 : 0 ≤ rwBlockLen e.k (ds e) / 2 := by
        have : 0 ≤ rwBlockLen e.k (ds e) := le_of_lt (rwBlockLen_pos e.k (ds e))
        nlinarith
      have : rewriteSlope e.k (ds e) * (rwBlockLen e.k (ds e) / 2) ≤ 1 * (rwBlockLen e.k (ds e) / 2) := by
        exact mul_le_mul_of_nonneg_right (le_of_lt hm1) hlen0
      nlinarith [this]
    have :
        y (Table.DeterministicNext.hitPoint (table e) (startState e) t) +
            x (Table.DeterministicNext.hitPoint (table e) (startState e) t) ≤
          (2 : ℝ) + rwBlockLen e.k (ds e) / 2 + (rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e)) := by
      simp [belowFlightLineRight1, hx, hy]
      nlinarith [h0, ht]
    simpa [hcur] using this

/-! ## No earlier boundary hits (segment-level) -/

theorem no_rwWallSameKCanonicalNoEndpoint_hit_before_two (e : Entry) {t : ℝ}
    (ht0 : 0 < t) (ht2 : t < 2) :
    Table.DeterministicNext.hitPoint (table e) (startState e) t ∉ rwWallUnionCanonicalNoEndpoint e.cur := by
  classical
  intro hmem
  rcases hmem with ⟨k', pref', hdigits, hpWall, hendpoint⟩
  -- Put the hit point in the appropriate “below-flight” half-space.
  have ht0' : 0 ≤ t := le_of_lt ht0
  have hbelow :
      Table.DeterministicNext.hitPoint (table e) (startState e) t ∈
        (if e.cur then belowFlightLineRight1 e.k (ds e) else belowFlightLineLeft0 e.k (ds e)) :=
    hitPoint_mem_belowFlightLine e ht0'
  cases hcur : e.cur
  · -- `cur=false`: use the endpoint-separation bound against walls strictly to the left.
    have hpBelow : Table.DeterministicNext.hitPoint (table e) (startState e) t ∈ belowFlightLineLeft0 e.k (ds e) := by
      simpa [hcur] using hbelow
    have hxTraj_lt : x (Table.DeterministicNext.hitPoint (table e) (startState e) t) < rwBlockLeft e.k (ds e) := by
      -- `x = left + (shiftRewrite/2)*t` and `shiftRewrite < 0`.
      have hlen_le : rwBlockLen e.k (ds e) ≤ (1 / 3 : ℝ) := by
        have hs : headScale e.k ≤ (1 / 3 : ℝ) := headScale_le_one_third e.k
        have hw : cantorWidth (ds e) ≤ (1 : ℝ) := cantorWidth_le_one (ds e)
        -- `rwBlockLen = headScale * cantorWidth`.
        simpa [rwBlockLen] using (mul_le_mul hs hw (by positivity) (by nlinarith [headScale_pos e.k]))
      have hshift_neg : shiftRewrite e.k (ds e) false < 0 := by
        -- `shiftRewrite = -2 + 2*len` and `len ≤ 1/3`.
        simp [shiftRewrite, shift] at *
        nlinarith [hlen_le]
      have hx :
          x (Table.DeterministicNext.hitPoint (table e) (startState e) t) =
            rwBlockLeft e.k (ds e) + (shiftRewrite e.k (ds e) false) / 2 * t := by
        simp [Table.DeterministicNext.hitPoint, startState, startPos, startVel, endpointY, hcur,
          Plane.x, Plane.eX, Plane.eY, Plane.mk, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm]
      -- since `(shiftRewrite/2)*t < 0` for `t>0`
      have : (shiftRewrite e.k (ds e) false) / 2 * t < 0 := by
        have : (shiftRewrite e.k (ds e) false) / 2 < 0 := by nlinarith [hshift_neg]
        exact mul_neg_of_neg_of_pos this ht0
      nlinarith [hx, this]
    rcases lt_trichotomy k' e.k with hklt | hkeq | hkgt
    · -- `k' < k`: use the cross-`k` endpoint separation bound (paper’s “hard” case).
      have hds : 0 < (ds e).length := by simp [ds]
      have hds' : 0 < (pref' ++ [false]).length := by simp
      have hsep :
          PaperReadWriteFlightAvoidanceCrossK.endpointSepCross e.k (ds e) k' (pref' ++ [false]) :=
        endpointSepCross_of_lt (k := e.k) (k' := k') hklt (ds := ds e) (ds' := pref' ++ [false]) hds hds'
      have hdis :=
        rwWall_false_disjoint_belowFlightLineLeft0_of_endpointSepCross (k := e.k) (ds := ds e) (k' := k')
          (ds' := pref' ++ [false]) hsep
      exact (Set.disjoint_left.1 hdis) ⟨hpWall, hendpoint⟩ hpBelow
    · -- `k' = k`: fall back to the same-level argument (as before).
      subst hkeq
      by_cases hpref : pref' = e.pref
      · subst hpref
        have hxWall_ge : rwBlockLeft e.k (ds e) ≤ x (Table.DeterministicNext.hitPoint (table e) (startState e) t) :=
          hpWall.1.1
        exact (not_lt_of_ge hxWall_ge) hxTraj_lt
      ·
        have hlenEq : (pref' ++ [false]).length = (e.pref ++ [false]).length := by
          simp [PaperReadWriteBoundary.rwDigits] at hdigits e.hlen
          simp [List.length_append, hdigits, e.hlen]
        have hne : (pref' ++ [false]) ≠ (e.pref ++ [false]) := by
          intro hEq
          apply hpref
          have := congrArg (fun l => l.take e.pref.length) hEq.symm
          simpa using this
        have hneL : rwBlockLeft e.k (ds e) ≠ rwBlockLeft e.k (pref' ++ [false]) := by
          exact rwBlockLeft_ne_of_length_eq (k := e.k) (ds := ds e) (ds' := pref' ++ [false]) hlenEq (by
            intro hdsEq
            apply hne
            simpa [ds] using hdsEq)
        have hlt : rwBlockLeft e.k (pref' ++ [false]) < rwBlockLeft e.k (ds e) ∨
            rwBlockLeft e.k (ds e) < rwBlockLeft e.k (pref' ++ [false]) :=
          lt_or_gt_of_ne hneL.symm
        rcases hlt with hleft | hright
        · have hsep : endpointSep e.k (ds e) (pref' ++ [false]) :=
            endpointSep_of_length_eq_of_left_gt (k := e.k) (ds := ds e) (ds' := pref' ++ [false]) hlenEq (by
              intro hEq; apply hne; simpa using hEq) hleft
          have hdis :=
            rwWall_false_disjoint_belowFlightLineLeft0_of_endpointSep (k := e.k) (ds := ds e) (ds' := pref' ++ [false])
              hsep
          exact (Set.disjoint_left.1 hdis) ⟨hpWall, hendpoint⟩ hpBelow
        · have hxWall_ge : rwBlockLeft e.k (pref' ++ [false]) ≤ x (Table.DeterministicNext.hitPoint (table e) (startState e) t) :=
            hpWall.1.1
          exact (not_lt_of_ge (le_trans hxTraj_lt.le (le_of_lt hright))) (lt_of_lt_of_le hright hxWall_ge)
    · -- `k < k'`: easy wrong-side exclusion by head-interval ordering + `x ≤ left`.
      have hx_le_left : x (Table.DeterministicNext.hitPoint (table e) (startState e) t) ≤ rwBlockLeft e.k (ds e) := by
        -- since `shiftRewrite < 0` and `t ≥ 0`
        have ht0' : 0 ≤ t := le_of_lt ht0
        have hlen_le : rwBlockLen e.k (ds e) ≤ (1 / 3 : ℝ) := by
          have hs : headScale e.k ≤ (1 / 3 : ℝ) := headScale_le_one_third e.k
          have hw : cantorWidth (ds e) ≤ (1 : ℝ) := cantorWidth_le_one (ds e)
          simpa [rwBlockLen] using (mul_le_mul hs hw (by positivity) (by nlinarith [headScale_pos e.k]))
        have hshift_neg : shiftRewrite e.k (ds e) false ≤ 0 := by
          simp [shiftRewrite, shift] at *
          nlinarith [hlen_le]
        have hx :
            x (Table.DeterministicNext.hitPoint (table e) (startState e) t) =
              rwBlockLeft e.k (ds e) + (shiftRewrite e.k (ds e) false) / 2 * t := by
          simp [Table.DeterministicNext.hitPoint, startState, startPos, startVel, endpointY, hcur,
            Plane.x, Plane.eX, Plane.eY, Plane.mk, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm]
        have : (shiftRewrite e.k (ds e) false) / 2 * t ≤ 0 := by
          have : (shiftRewrite e.k (ds e) false) / 2 ≤ 0 := by nlinarith [hshift_neg]
          exact mul_nonpos_of_nonpos_of_nonneg this ht0'
        nlinarith [hx, this]
      -- But any wall at index `k'` lives in `headInterval k'`, so `headLeft k' ≤ x`.
      have hxHead' : x (Table.DeterministicNext.hitPoint (table e) (startState e) t) ∈ headInterval k' :=
        (rwBlockInterval_subset_headInterval (k := k') (ds := pref' ++ [false])) hpWall.1
      have hx_ge : headLeft k' ≤ x (Table.DeterministicNext.hitPoint (table e) (startState e) t) := hxHead'.1
      have hleftHead : rwBlockLeft e.k (ds e) ∈ headInterval e.k := by
        have hx01 : cantorLeft (ds e) ∈ Set.Icc (0 : ℝ) 1 := ⟨cantorLeft_nonneg (ds e), cantorLeft_le_one (ds e)⟩
        simpa [rwBlockLeft] using (tau_mem_headInterval (k := e.k) (x := cantorLeft (ds e)) hx01)
      have hleft_le : rwBlockLeft e.k (ds e) ≤ headRight e.k := hleftHead.2
      have hsep : headRight e.k < headLeft k' := headRight_lt_headLeft_of_lt hkgt
      have hx_gt : rwBlockLeft e.k (ds e) < x (Table.DeterministicNext.hitPoint (table e) (startState e) t) :=
        lt_of_le_of_lt hleft_le (lt_of_lt_of_le hsep hx_ge)
      exact (not_lt_of_ge hx_le_left) hx_gt
  · -- `cur=true`: symmetric.
    have hpBelow : Table.DeterministicNext.hitPoint (table e) (startState e) t ∈ belowFlightLineRight1 e.k (ds e) := by
      simpa [hcur] using hbelow
    have hxTraj_gt : rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e) < x (Table.DeterministicNext.hitPoint (table e) (startState e) t) := by
      -- `x = right + (shiftRewrite/2)*t` and `shiftRewrite > 0`.
      have hlen_le : rwBlockLen e.k (ds e) ≤ (1 / 3 : ℝ) := by
        have hs : headScale e.k ≤ (1 / 3 : ℝ) := headScale_le_one_third e.k
        have hw : cantorWidth (ds e) ≤ (1 : ℝ) := cantorWidth_le_one (ds e)
        simpa [rwBlockLen] using (mul_le_mul hs hw (by positivity) (by nlinarith [headScale_pos e.k]))
      have hshift_pos : 0 < shiftRewrite e.k (ds e) true := by
        simp [shiftRewrite, shift] at *
        nlinarith [hlen_le]
      have hx :
          x (Table.DeterministicNext.hitPoint (table e) (startState e) t) =
            (rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e)) + (shiftRewrite e.k (ds e) true) / 2 * t := by
        simp [Table.DeterministicNext.hitPoint, startState, startPos, startVel, endpointY, hcur,
          Plane.x, Plane.eX, Plane.eY, Plane.mk, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm]
      have : 0 < (shiftRewrite e.k (ds e) true) / 2 * t := by
        have : 0 < (shiftRewrite e.k (ds e) true) / 2 := by nlinarith [hshift_pos]
        exact mul_pos this ht0
      nlinarith [hx, this]
    -- Trichotomy in the head index (now `k'` is part of the wall witness).
    rcases lt_trichotomy e.k k' with hklt | hkeq | hkgt
    · -- `k < k'`: cross-`k` endpoint separation, with roles swapped.
      have hds : 0 < (pref' ++ [true]).length := by simp
      have hds' : 0 < (ds e).length := by simp [ds]
      have hsep :
          PaperReadWriteFlightAvoidanceCrossK.endpointSepCross k' (pref' ++ [true]) e.k (ds e) :=
        endpointSepCross_of_lt (k := k') (k' := e.k) hklt (ds := pref' ++ [true]) (ds' := ds e) hds hds'
      have hdis :=
        rwWall_true_disjoint_belowFlightLineRight1_of_endpointSepCross (k := e.k) (ds := ds e) (k' := k')
          (ds' := pref' ++ [true]) hsep
      exact (Set.disjoint_left.1 hdis) ⟨hpWall, hendpoint⟩ hpBelow
    · -- `k' = k`: same-level argument as before.
      subst hkeq
      by_cases hpref : pref' = e.pref
      · subst hpref
        have hxWall_le :
            x (Table.DeterministicNext.hitPoint (table e) (startState e) t) ≤
              rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e) := hpWall.1.2
        exact (not_lt_of_ge hxWall_le) hxTraj_gt
      ·
        have hlenEq : (pref' ++ [true]).length = (e.pref ++ [true]).length := by
          simp [PaperReadWriteBoundary.rwDigits] at hdigits e.hlen
          simp [List.length_append, hdigits, e.hlen]
        have hne : (pref' ++ [true]) ≠ (e.pref ++ [true]) := by
          intro hEq
          apply hpref
          have := congrArg (fun l => l.take e.pref.length) hEq.symm
          simpa using this
        have hneL : rwBlockLeft e.k (ds e) ≠ rwBlockLeft e.k (pref' ++ [true]) := by
          exact rwBlockLeft_ne_of_length_eq (k := e.k) (ds := ds e) (ds' := pref' ++ [true]) hlenEq (by
            intro hdsEq
            apply hne
            simpa [ds] using hdsEq)
        have hlt : rwBlockLeft e.k (pref' ++ [true]) < rwBlockLeft e.k (ds e) ∨
            rwBlockLeft e.k (ds e) < rwBlockLeft e.k (pref' ++ [true]) :=
          lt_or_gt_of_ne hneL.symm
        rcases hlt with hleft | hright
        · -- Wall lies to the left: `x ≥ right(ds)` keeps us away.
          have hxWall_le :
              x (Table.DeterministicNext.hitPoint (table e) (startState e) t) ≤
                rwBlockLeft e.k (pref' ++ [true]) + rwBlockLen e.k (pref' ++ [true]) := hpWall.1.1.2
          have hlenLen : rwBlockLen e.k (pref' ++ [true]) = rwBlockLen e.k (ds e) :=
            rwBlockLen_eq_of_length_eq (k := e.k) (ds := pref' ++ [true]) (ds' := ds e) hlenEq
          have : rwBlockLeft e.k (pref' ++ [true]) + rwBlockLen e.k (pref' ++ [true]) <
              rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e) := by
            nlinarith [hleft, hlenLen]
          exact (not_lt_of_ge hxWall_le) (lt_of_lt_of_le this hxTraj_gt.le)
        · -- Wall lies to the right: apply endpoint separation (swapped) and the below-halfspace lemma.
          have hsep : endpointSep e.k (pref' ++ [true]) (ds e) :=
            endpointSep_of_length_eq_of_left_gt (k := e.k) (ds := pref' ++ [true]) (ds' := ds e) hlenEq.symm (by
              intro hEq
              apply hne
              simpa using hEq) (by simpa using hright)
          have hdis :=
            rwWall_true_disjoint_belowFlightLineRight1_of_endpointSep (k := e.k) (ds := ds e) (ds' := pref' ++ [true])
              hsep
          exact (Set.disjoint_left.1 hdis) ⟨hpWall, hendpoint⟩ hpBelow
    · -- `k' < k`: easy wrong-side exclusion by head-interval ordering + `right ≤ x`.
      have hx_ge_right :
          rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e) ≤
            x (Table.DeterministicNext.hitPoint (table e) (startState e) t) := by
        have ht0' : 0 ≤ t := le_of_lt ht0
        have hlen_le : rwBlockLen e.k (ds e) ≤ (1 / 3 : ℝ) := by
          have hs : headScale e.k ≤ (1 / 3 : ℝ) := headScale_le_one_third e.k
          have hw : cantorWidth (ds e) ≤ (1 : ℝ) := cantorWidth_le_one (ds e)
          simpa [rwBlockLen] using (mul_le_mul hs hw (by positivity) (by nlinarith [headScale_pos e.k]))
        have hshift_pos : 0 ≤ shiftRewrite e.k (ds e) true := by
          simp [shiftRewrite, shift] at *
          nlinarith [hlen_le]
        have hx :
            x (Table.DeterministicNext.hitPoint (table e) (startState e) t) =
              (rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e)) + (shiftRewrite e.k (ds e) true) / 2 * t := by
          simp [Table.DeterministicNext.hitPoint, startState, startPos, startVel, endpointY, hcur,
            Plane.x, Plane.eX, Plane.eY, Plane.mk, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm]
        have : 0 ≤ (shiftRewrite e.k (ds e) true) / 2 * t := by
          have : 0 ≤ (shiftRewrite e.k (ds e) true) / 2 := by nlinarith [hshift_pos]
          exact mul_nonneg this ht0'
        nlinarith [hx, this]
      have hxHead' :
          x (Table.DeterministicNext.hitPoint (table e) (startState e) t) ∈ headInterval k' :=
        (rwBlockInterval_subset_headInterval (k := k') (ds := pref' ++ [true])) hpWall.1
      have hx_le : x (Table.DeterministicNext.hitPoint (table e) (startState e) t) ≤ headRight k' := hxHead'.2
      have hrightHead : (rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e)) ∈ headInterval e.k := by
        have hx01 : (cantorLeft (ds e) + cantorWidth (ds e)) ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨by
            have h0 : 0 ≤ cantorLeft (ds e) := cantorLeft_nonneg (ds e)
            have h1 : 0 ≤ cantorWidth (ds e) := by
              unfold cantorWidth
              have : 0 < (3 : ℝ) ^ (ds e).length := by positivity
              exact le_of_lt (inv_pos.2 this)
            linarith, cantorLeft_add_width_le_one (ds e)⟩
        have ht :
            tau e.k (cantorLeft (ds e) + cantorWidth (ds e)) =
              rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e) := by
          simp [rwBlockLeft, rwBlockLen, tau_eq_affine, cantorWidth, mul_add, add_assoc, add_left_comm, add_comm]
        simpa [headInterval] using (ht ▸ tau_mem_headInterval (k := e.k) (x := cantorLeft (ds e) + cantorWidth (ds e)) hx01)
      have hright_ge : headLeft e.k ≤ rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e) := hrightHead.1
      have hsep : headRight k' < headLeft e.k := headRight_lt_headLeft_of_lt hkgt
      have : x (Table.DeterministicNext.hitPoint (table e) (startState e) t) < rwBlockLeft e.k (ds e) + rwBlockLen e.k (ds e) :=
        lt_of_le_of_lt hx_le (lt_of_lt_of_le hsep hright_ge)
      exact (not_lt_of_ge hx_ge_right) this

/-! ### Redirecting-wall union: segment-level “no earlier hits” (fixed `k`) -/

theorem y_le_rewriteSlope_mul_half_rwBlockLen_of_mem_tildeWallRewriteAppendix
    (k : ℤ) (ds : List Bool) (cur : Bool) {p : V} (hp : p ∈ tildeWallRewriteAppendix k ds cur) :
    y p ≤ rewriteSlope k ds * (rwBlockLen k ds) / 2 := by
  rcases hp with ⟨hx, hy⟩
  -- Convert `x` bounds to bounds on the centered coordinate.
  have hx' : x p - shiftRewrite k ds cur ∈ rwBlockInterval k ds := by
    rcases hx with ⟨hxL, hxU⟩
    constructor <;> linarith
  have hcenter :
      |(if cur then (x p - shiftRewrite k ds cur) - rwBlockCenter k ds
        else rwBlockCenter k ds - (x p - shiftRewrite k ds cur))| ≤ (rwBlockLen k ds) / 2 := by
    -- In either branch, the term is (signed) distance from the center, bounded by `len/2`.
    rcases hx' with ⟨hxL, hxU⟩
    have hlen0 : 0 ≤ rwBlockLen k ds := le_of_lt (rwBlockLen_pos k ds)
    have hhalf0 : 0 ≤ (rwBlockLen k ds) / 2 := by nlinarith
    cases cur <;>
      -- `simp` turns the goal into a linear inequality.
      simp [rwBlockCenter, abs_sub_comm, abs_le, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] <;>
      nlinarith [hxL, hxU, hlen0, hhalf0]
  -- Multiply the absolute bound by `rewriteSlope` and discard signs.
  have hm0 : 0 ≤ rewriteSlope k ds := by
    have hlen : 0 < rwBlockLen k ds := rwBlockLen_pos k ds
    have : 0 < (1 : ℝ) + rwBlockLen k ds := by linarith
    have : 0 < rewriteSlope k ds := by simp [rewriteSlope, one_div, inv_pos.2 this]
    exact le_of_lt this
  -- Use `|y| ≤ m*len/2` and conclude `y ≤ m*len/2`.
  have hyabs :
      |y p| ≤ rewriteSlope k ds * (rwBlockLen k ds) / 2 := by
    cases cur <;>
      simp [tildeWallRewriteAppendix, hy, abs_mul, abs_of_nonneg hm0] at hcenter ⊢ <;>
      nlinarith [hcenter]
  exact le_trans (le_abs_self (y p)) hyabs

theorem no_tildeWallRewriteAppendixUnionCanonicalAt_hit_before_two (e : Entry) {t : ℝ}
    (ht0 : 0 < t) (ht2 : t < 2) :
    Table.DeterministicNext.hitPoint (table e) (startState e) t ∉
      tildeWallRewriteAppendixUnionCanonicalAt e.k e.cur := by
  classical
  intro hmem
  rcases hmem with ⟨pref', hdigits, hp⟩
  -- All walls in the fixed-`k` canonical union have the same length as `ds e`.
  have hlenEq : (pref' ++ [e.cur]).length = (ds e).length := by
    simp [PaperReadWriteBoundary.rwDigits] at hdigits e.hlen
    simp [ds, List.length_append, hdigits, e.hlen]
  have hlen : rwBlockLen e.k (pref' ++ [e.cur]) = rwBlockLen e.k (ds e) := by
    simpa using (rwBlockLen_eq_of_length_eq (k := e.k) (ds := pref' ++ [e.cur]) (ds' := ds e) hlenEq)
  have hm : rewriteSlope e.k (pref' ++ [e.cur]) = rewriteSlope e.k (ds e) := by
    simp [rewriteSlope, hlen]
  -- Bound `y` on the redirecting wall, then compare to the trajectory’s explicit `y`.
  have hyWall :
      y (Table.DeterministicNext.hitPoint (table e) (startState e) t) ≤
        rewriteSlope e.k (ds e) * (rwBlockLen e.k (ds e)) / 2 := by
    have := y_le_rewriteSlope_mul_half_rwBlockLen_of_mem_tildeWallRewriteAppendix
      (k := e.k) (ds := pref' ++ [e.cur]) (cur := e.cur)
      (p := Table.DeterministicNext.hitPoint (table e) (startState e) t) hp
    simpa [hm, hlen] using this
  have hyTraj :
      y (Table.DeterministicNext.hitPoint (table e) (startState e) t) =
        (2 : ℝ) + rewriteSlope e.k (ds e) * rwBlockLen e.k (ds e) / 2 - t := by
    -- This is the same computation as in `hitPoint_mem_belowFlightLine`.
    cases hcur : e.cur <;>
      simp [Table.DeterministicNext.hitPoint, startState, startPos, startVel, endpointY, hcur,
        Plane.y, Plane.eX, Plane.eY, Plane.mk] <;>
      ring_nf
  have hygt :
      rewriteSlope e.k (ds e) * (rwBlockLen e.k (ds e)) / 2 <
        y (Table.DeterministicNext.hitPoint (table e) (startState e) t) := by
    -- `t < 2` implies `2 - t > 0`, hence the trajectory `y` is strictly above the wall’s maximum.
    have : 0 < (2 : ℝ) - t := sub_pos.2 ht2
    nlinarith [hyTraj, this]
  exact (not_lt_of_ge hyWall) hygt

theorem no_boundary_hit_before_two (e : Entry) {t : ℝ} (ht0 : 0 < t) (ht2 : t < 2) :
    Table.DeterministicNext.hitPoint (table e) (startState e) t ∉ (table e).boundary := by
  intro hmem
  rcases hmem with hmem | hmem
  · exact no_rwWallSameKCanonicalNoEndpoint_hit_before_two e ht0 ht2 hmem
  · exact no_tildeWallRewriteAppendixUnionCanonicalAt_hit_before_two e ht0 ht2 hmem

theorem start_Good_firstHit (e : Entry) :
    Table.DeterministicNext.Good (table e) (startState e) := by
  classical
  refine ExistsUnique.intro (2 : ℝ) ?exist ?uniq
  · refine And.intro ?hit ?noEarlier
    · refine ⟨by norm_num, ?_⟩
      refine ⟨hitPoint₂_mem_boundary e, ?_⟩
      simp [Table.DeterministicNext.IsHitTime, Table.DeterministicNext.hitPoint, table, startState, hitPoint₂,
        Billiards.Table.Flight]
    · intro t ht0 htlt
      exact no_boundary_hit_before_two e ht0 (lt_of_lt_of_le htlt (by norm_num))
  · intro t htFirst
    -- Any first-hit time must satisfy `t ≤ 2` since `2` is a hit time, and cannot be `< 2`.
    have hhit2 : Table.DeterministicNext.IsHitTime (table e) (startState e) 2 := by
      refine ⟨by norm_num, ?_⟩
      refine ⟨hitPoint₂_mem_boundary e, ?_⟩
      simp [Table.DeterministicNext.hitPoint, table, startState, hitPoint₂, Billiards.Table.Flight]
    have ht_le : t ≤ 2 := by
      -- If `t > 2`, then `2` would be an earlier boundary hit, contradicting first-hit minimality.
      by_contra hgt
      have hlt : 2 < t := lt_of_not_ge hgt
      have : Table.DeterministicNext.hitPoint (table e) (startState e) 2 ∉ (table e).boundary :=
        (htFirst.2) 2 (by norm_num) hlt
      exact this (hhit2.2.1)
    have ht_ge : 2 ≤ t := by
      -- If `t < 2`, then there is no boundary hit at time `t` by `no_boundary_hit_before_two`.
      by_contra hlt
      have htlt : t < 2 := lt_of_not_ge hlt
      have htpos : 0 < t := htFirst.1.1
      have : Table.DeterministicNext.hitPoint (table e) (startState e) t ∉ (table e).boundary :=
        no_boundary_hit_before_two e htpos htlt
      exact this (htFirst.1.2.1)
    exact le_antisymm ht_le ht_ge

theorem next?_eq_some (e : Entry) :
    Table.DeterministicNext.next? (table e) (startState e) =
      some ⟨hitPoint₂ e, reflect (rwWallRewriteNormal e.k (ds e) e.cur) (startVel e)⟩ := by
  classical
  have hgood : Table.DeterministicNext.Good (table e) (startState e) := start_Good_firstHit e
  -- Now compute `next?` by uniqueness of the first-hit time.
  have hq : Table.DeterministicNext.hitPoint (table e) (startState e) 2 ∈ (table e).boundary :=
    hitPoint₂_mem_boundary e
  simp [Table.DeterministicNext.next?, hgood, Table.DeterministicNext.hitPoint, startState, hitPoint₂, startVel, table,
    hq]

-- The old single-wall lemma `no_intendedTilde_hit_before_two` is superseded by the union-level
-- y-bound argument above.
end RewriteBetween

end PaperReadWrite

end Billiards
end MirandaDynamics
end HeytingLean
