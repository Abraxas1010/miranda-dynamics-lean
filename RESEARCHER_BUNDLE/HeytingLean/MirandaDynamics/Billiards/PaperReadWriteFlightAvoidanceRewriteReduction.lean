import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteFlightAvoidanceCrossK

/-!
# MirandaDynamics.Billiards: rewrite-flight avoidance reduction to read-only extremal rays (WS7.3)

The Appendix claims that “symbol change” trajectories descend more steeply than the read-only case,
so collision avoidance is strictly easier: it suffices to check the read-only extremal rays.

This file isolates a mechanizable core of that reduction:

* replace the read-only extremal **line** constraint (`=`) by a half-space constraint (`≤`) which
  encodes “below the read-only extremal flight line”;
* show the usual endpoint-separation inequality `endpointSep` already forces any intersection with
  a wall segment to occur at a singular endpoint; hence the wall interior is disjoint from this
  half-space.

Downstream deterministic-next constructions can then show that a rewrite between-wall trajectory
stays inside this half-space, and therefore cannot collide with any other separating wall.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set
open Plane

namespace PaperReadWrite

/-! ## “Below” half-spaces associated to the read-only extremal flight lines -/

/-- The closed half-space “at or below” `flightLineLeft0 k ds`. -/
def belowFlightLineLeft0 (k : ℤ) (ds : List Bool) : Set V :=
  { p | y p - x p ≤ (2 : ℝ) + (rwBlockLen k ds) / 2 - rwBlockLeft k ds }

/-- The closed half-space “at or below” `flightLineRight1 k ds`. -/
def belowFlightLineRight1 (k : ℤ) (ds : List Bool) : Set V :=
  { p | y p + x p ≤ (2 : ℝ) + (rwBlockLen k ds) / 2 + (rwBlockLeft k ds + rwBlockLen k ds) }

/-! ## Endpoint-separation forces wall interiors to lie strictly above these half-spaces -/

theorem rwWall_false_mem_belowFlightLineLeft0_imp_rightEndpoint_of_endpointSep (k : ℤ) (ds ds' : List Bool)
    (hsep : endpointSep k ds ds') {p : V}
    (hpWall : p ∈ rwWall k ds' false) (hpBelow : p ∈ belowFlightLineLeft0 k ds) :
    x p = rwBlockLeft k ds' + rwBlockLen k ds' := by
  -- Expand `y - x` using the wall equation and compare to the flight-line bound.
  have hyWall : y p = (2 : ℝ) + (rwBlockCenter k ds' - x p) := by
    simpa [rwWall] using hpWall.2
  have hle :
      (2 : ℝ) + (rwBlockCenter k ds' - x p) - x p ≤ (2 : ℝ) + (rwBlockLen k ds) / 2 - rwBlockLeft k ds := by
    -- `y - x = (2 + center' - x) - x`.
    have : y p - x p = (2 : ℝ) + (rwBlockCenter k ds' - x p) - x p := by
      linarith [hyWall]
    -- Use the half-space hypothesis.
    simpa [belowFlightLineLeft0, this] using hpBelow
  -- Solve for `x p` from the inequality and combine with `endpointSep`.
  have hx_ge :
      x p ≥ rwBlockLeft k ds' + rwBlockLen k ds' := by
    -- `endpointSep` gives: `rwBlockLeft ds - (rwBlockLeft ds' + len') ≥ len/2 + len'/2`.
    -- Together with `hle` it forces `x ≥ rightEndpoint(ds')`.
    dsimp [endpointSep] at hsep
    have hcenter : rwBlockCenter k ds' = rwBlockLeft k ds' + (rwBlockLen k ds') / 2 := by
      simp [rwBlockCenter]
    -- Direct linear arithmetic.
    nlinarith [hle, hsep, hcenter]
  have hx_le : x p ≤ rwBlockLeft k ds' + rwBlockLen k ds' := hpWall.1.2
  exact le_antisymm hx_le hx_ge

theorem rwWall_false_disjoint_belowFlightLineLeft0_of_endpointSep (k : ℤ) (ds ds' : List Bool)
    (hsep : endpointSep k ds ds') :
    Disjoint (rwWall k ds' false ∩ {p : V | x p < rwBlockLeft k ds' + rwBlockLen k ds'}) (belowFlightLineLeft0 k ds) := by
  classical
  refine Set.disjoint_left.2 ?_
  intro p hpWall hpBelow
  have hp : p ∈ rwWall k ds' false := hpWall.1
  have hx :
      x p = rwBlockLeft k ds' + rwBlockLen k ds' :=
    rwWall_false_mem_belowFlightLineLeft0_imp_rightEndpoint_of_endpointSep (k := k) (ds := ds) (ds' := ds')
      hsep hp hpBelow
  exact (not_lt_of_eq hx) hpWall.2

theorem rwWall_true_mem_belowFlightLineRight1_imp_leftEndpoint_of_endpointSep (k : ℤ) (ds ds' : List Bool)
    (hsep : endpointSep k ds' ds) {p : V}
    (hpWall : p ∈ rwWall k ds' true) (hpBelow : p ∈ belowFlightLineRight1 k ds) :
    x p = rwBlockLeft k ds' := by
  have hyWall : y p = (2 : ℝ) + (-rwBlockCenter k ds' + x p) := by
    simpa [rwWall] using hpWall.2
  have hle :
      (2 : ℝ) + (-rwBlockCenter k ds' + x p) + x p ≤
        (2 : ℝ) + (rwBlockLen k ds) / 2 + (rwBlockLeft k ds + rwBlockLen k ds) := by
    have : y p + x p = (2 : ℝ) + (-rwBlockCenter k ds' + x p) + x p := by
      linarith [hyWall]
    simpa [belowFlightLineRight1, this] using hpBelow
  have hx_le : x p ≤ rwBlockLeft k ds' := by
    dsimp [endpointSep] at hsep
    have hcenter : rwBlockCenter k ds' = rwBlockLeft k ds' + (rwBlockLen k ds') / 2 := by
      simp [rwBlockCenter]
    nlinarith [hle, hsep, hcenter]
  have hx_ge : rwBlockLeft k ds' ≤ x p := hpWall.1.1
  exact le_antisymm hx_le hx_ge

theorem rwWall_true_disjoint_belowFlightLineRight1_of_endpointSep (k : ℤ) (ds ds' : List Bool)
    (hsep : endpointSep k ds' ds) :
    Disjoint (rwWall k ds' true ∩ {p : V | rwBlockLeft k ds' < x p}) (belowFlightLineRight1 k ds) := by
  classical
  refine Set.disjoint_left.2 ?_
  intro p hpWall hpBelow
  have hp : p ∈ rwWall k ds' true := hpWall.1
  have hx :
      x p = rwBlockLeft k ds' :=
    rwWall_true_mem_belowFlightLineRight1_imp_leftEndpoint_of_endpointSep (k := k) (ds := ds) (ds' := ds')
      hsep hp hpBelow
  exact (not_lt_of_eq hx.symm) hpWall.2

/-!
## Cross-`k` variants (endpoint separation across head intervals)

`PaperReadWriteFlightAvoidanceCrossK` packages quantitative inequalities yielding `endpointSepCross`
for ordered head indices. The following lemmas lift the same “rewrite is easier” half-space argument
to that cross-`k` setting.
-/

open PaperReadWriteFlightAvoidanceCrossK

theorem rwWall_false_mem_belowFlightLineLeft0_imp_rightEndpoint_of_endpointSepCross
    (k : ℤ) (ds : List Bool) (k' : ℤ) (ds' : List Bool)
    (hsep : endpointSepCross k ds k' ds') {p : V}
    (hpWall : p ∈ rwWall k' ds' false) (hpBelow : p ∈ belowFlightLineLeft0 k ds) :
    x p = rwBlockLeft k' ds' + rwBlockLen k' ds' := by
  have hyWall : y p = (2 : ℝ) + (rwBlockCenter k' ds' - x p) := by
    simpa [rwWall] using hpWall.2
  have hle :
      (2 : ℝ) + (rwBlockCenter k' ds' - x p) - x p ≤ (2 : ℝ) + (rwBlockLen k ds) / 2 - rwBlockLeft k ds := by
    have : y p - x p = (2 : ℝ) + (rwBlockCenter k' ds' - x p) - x p := by
      linarith [hyWall]
    simpa [belowFlightLineLeft0, this] using hpBelow
  have hx_ge : x p ≥ rwBlockLeft k' ds' + rwBlockLen k' ds' := by
    -- `endpointSepCross` + the inequality form suffices.
    dsimp [endpointSepCross, PaperReadWrite.endpointSepCross] at hsep
    have hcenter : rwBlockCenter k' ds' = rwBlockLeft k' ds' + (rwBlockLen k' ds') / 2 := by
      simp [rwBlockCenter]
    nlinarith [hle, hsep, hcenter]
  have hx_le : x p ≤ rwBlockLeft k' ds' + rwBlockLen k' ds' := hpWall.1.2
  exact le_antisymm hx_le hx_ge

theorem rwWall_false_disjoint_belowFlightLineLeft0_of_endpointSepCross
    (k : ℤ) (ds : List Bool) (k' : ℤ) (ds' : List Bool)
    (hsep : endpointSepCross k ds k' ds') :
    Disjoint (rwWall k' ds' false ∩ {p : V | x p < rwBlockLeft k' ds' + rwBlockLen k' ds'})
      (belowFlightLineLeft0 k ds) := by
  classical
  refine Set.disjoint_left.2 ?_
  intro p hpWall hpBelow
  have hx :
      x p = rwBlockLeft k' ds' + rwBlockLen k' ds' :=
    rwWall_false_mem_belowFlightLineLeft0_imp_rightEndpoint_of_endpointSepCross
      (k := k) (ds := ds) (k' := k') (ds' := ds') hsep hpWall.1 hpBelow
  exact (not_lt_of_ge (by simpa [hx] using le_rfl)) hpWall.2

theorem rwWall_true_mem_belowFlightLineRight1_imp_leftEndpoint_of_endpointSepCross
    (k : ℤ) (ds : List Bool) (k' : ℤ) (ds' : List Bool)
    (hsep : endpointSepCross k' ds' k ds) {p : V}
    (hpWall : p ∈ rwWall k' ds' true) (hpBelow : p ∈ belowFlightLineRight1 k ds) :
    x p = rwBlockLeft k' ds' := by
  have hyWall : y p = (2 : ℝ) + (-rwBlockCenter k' ds' + x p) := by
    simpa [rwWall] using hpWall.2
  have hle :
      (2 : ℝ) + (-rwBlockCenter k' ds' + x p) + x p ≤
        (2 : ℝ) + (rwBlockLen k ds) / 2 + (rwBlockLeft k ds + rwBlockLen k ds) := by
    have : y p + x p = (2 : ℝ) + (-rwBlockCenter k' ds' + x p) + x p := by
      linarith [hyWall]
    simpa [belowFlightLineRight1, this] using hpBelow
  have hx_le : x p ≤ rwBlockLeft k' ds' := by
    dsimp [endpointSepCross, PaperReadWrite.endpointSepCross] at hsep
    have hcenter : rwBlockCenter k' ds' = rwBlockLeft k' ds' + (rwBlockLen k' ds') / 2 := by
      simp [rwBlockCenter]
    nlinarith [hle, hsep, hcenter]
  have hx_ge : rwBlockLeft k' ds' ≤ x p := hpWall.1.1
  exact le_antisymm hx_le hx_ge

theorem rwWall_true_disjoint_belowFlightLineRight1_of_endpointSepCross
    (k : ℤ) (ds : List Bool) (k' : ℤ) (ds' : List Bool)
    (hsep : endpointSepCross k' ds' k ds) :
    Disjoint (rwWall k' ds' true ∩ {p : V | rwBlockLeft k' ds' < x p}) (belowFlightLineRight1 k ds) := by
  classical
  refine Set.disjoint_left.2 ?_
  intro p hpWall hpBelow
  have hx :
      x p = rwBlockLeft k' ds' :=
    rwWall_true_mem_belowFlightLineRight1_imp_leftEndpoint_of_endpointSepCross
      (k := k) (ds := ds) (k' := k') (ds' := ds') hsep hpWall.1 hpBelow
  exact (not_lt_of_ge (by simpa [hx] using le_rfl)) hpWall.2

end PaperReadWrite

end Billiards
end MirandaDynamics
end HeytingLean
