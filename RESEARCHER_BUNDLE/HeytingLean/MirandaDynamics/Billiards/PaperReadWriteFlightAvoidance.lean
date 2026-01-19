import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteNoSpurious

/-!
# MirandaDynamics.Billiards: Appendix-style straight-wall flight avoidance (WS7.3)

The Appendix “no spurious collisions” argument compares an *extremal* post-bounce trajectory
against endpoints of other wall segments.

This file packages the first reusable lemma of that style:

* for `cur=false` (slope `-1` read-only walls), consider the line of slope `+1` passing through the
  **left endpoint** of a wall;
* under the endpoint-separation inequality `endpointSep`, that line cannot meet any other
  same-level (`k`), same-cur wall segment except possibly at a boundary endpoint.

This isolates the exact inequality shape used in the paper (and already packaged as
`PaperReadWrite.endpointSep`).
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set
open Plane

namespace PaperReadWrite

/-! ## The “extremal” flight line (cur=false case) -/

/-- The line of slope `+1` passing through the *left endpoint* of `rwWall k ds false`. -/
def flightLineLeft0 (k : ℤ) (ds : List Bool) : Set V :=
  { p | y p - x p = (2 : ℝ) + (rwBlockLen k ds) / 2 - rwBlockLeft k ds }

theorem mem_flightLineLeft0_iff (k : ℤ) (ds : List Bool) (p : V) :
    p ∈ flightLineLeft0 k ds ↔ y p - x p = (2 : ℝ) + (rwBlockLen k ds) / 2 - rwBlockLeft k ds := Iff.rfl

/-! ## A ray version (the line restricted to the down-left direction) -/

/-- The ray starting at the left endpoint directionally moving down-left: the `flightLineLeft0`
equation plus the monotonicity constraint `x ≤ left`. -/
def flightRayLeft0 (k : ℤ) (ds : List Bool) : Set V :=
  flightLineLeft0 k ds ∩ { p | x p ≤ rwBlockLeft k ds }

theorem flightRayLeft0_subset_flightLineLeft0 (k : ℤ) (ds : List Bool) :
    flightRayLeft0 k ds ⊆ flightLineLeft0 k ds := by
  intro p hp
  exact hp.1

/-! ## Intersection control via `endpointSep` -/

theorem rwWall_false_mem_flightLineLeft0_imp_rightEndpoint (k : ℤ) (ds ds' : List Bool)
    (hlen : ds.length = ds'.length) (hsep : endpointSep k ds ds') {p : V}
    (hpWall : p ∈ rwWall k ds' false) (hpFlight : p ∈ flightLineLeft0 k ds) :
    x p = rwBlockLeft k ds' + rwBlockLen k ds' := by
  -- Unpack the wall equation and combine with the flight-line equation.
  have hyWall : y p = (2 : ℝ) + (rwBlockCenter k ds' - x p) := by
    simpa [rwWall] using hpWall.2
  have hyFlight : y p - x p = (2 : ℝ) + (rwBlockLen k ds) / 2 - rwBlockLeft k ds := hpFlight
  -- Compute `x p` from the two equalities:
  -- `y - x = 2 + center' - 2x` and `y - x = 2 + len/2 - left`.
  have hxEq :
      2 * x p = rwBlockCenter k ds' + rwBlockLeft k ds - (rwBlockLen k ds) / 2 := by
    -- Rewrite `y - x` using the wall equation, then equate to the flight constant.
    have : (2 : ℝ) + (rwBlockCenter k ds' - x p) - x p =
        (2 : ℝ) + (rwBlockLen k ds) / 2 - rwBlockLeft k ds := by
      -- Expand `y - x` using `hyWall`, then use `hyFlight`.
      have : y p - x p = (2 : ℝ) + (rwBlockCenter k ds' - x p) - x p := by
        linarith [hyWall]
      -- Combine.
      linarith [this, hyFlight]
    -- Rearrange.
    linarith [this]
  -- Use the common length to rewrite `rwBlockCenter`.
  have hlenLen : rwBlockLen k ds' = rwBlockLen k ds := rwBlockLen_eq_of_length_eq (k := k) (ds := ds') (ds' := ds) hlen.symm
  have hcenter : rwBlockCenter k ds' = rwBlockLeft k ds' + (rwBlockLen k ds) / 2 := by
    simp [rwBlockCenter, hlenLen]
  have hxForm : x p = (rwBlockLeft k ds' + rwBlockLeft k ds) / 2 := by
    have : x p = (rwBlockCenter k ds' + rwBlockLeft k ds - (rwBlockLen k ds) / 2) / 2 := by
      linarith [hxEq]
    -- Substitute `rwBlockCenter = left' + len/2`.
    simpa [hcenter, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  -- `endpointSep` implies `left - (left' + len') ≥ len/2 + len'/2`, hence `left - left' ≥ len + ...`.
  have hgap : rwBlockLeft k ds - rwBlockLeft k ds' ≥ 2 * rwBlockLen k ds := by
    -- From `endpointSep` and equal lengths: `left - left' - len ≥ len`, so `left - left' ≥ 2*len`.
    dsimp [endpointSep] at hsep
    -- Replace `len'` with `len`.
    have : rwBlockLeft k ds - (rwBlockLeft k ds' + rwBlockLen k ds) ≥ rwBlockLen k ds := by
      -- RHS becomes `len/2 + len/2 = len`.
      nlinarith [hsep, hlenLen]
    -- Now add `left'` and rearrange.
    nlinarith [this]
  -- Show `x p ≥ left' + len`.
  have hx_ge : x p ≥ rwBlockLeft k ds' + rwBlockLen k ds' := by
    -- Use `hxForm` and `hgap`.
    have : (rwBlockLeft k ds' + rwBlockLeft k ds) / 2 ≥ rwBlockLeft k ds' + rwBlockLen k ds := by
      nlinarith [hgap]
    simpa [hxForm, hlenLen] using this
  -- But wall membership gives `x p ≤ left' + len'`.
  have hx_le : x p ≤ rwBlockLeft k ds' + rwBlockLen k ds' := hpWall.1.2
  exact le_antisymm hx_le hx_ge

/-- A length-free version of `rwWall_false_mem_flightLineLeft0_imp_rightEndpoint`:
the endpoint-separation inequality alone forces the intersection to occur at the **right endpoint**
of the (potentially different-length) wall segment. -/
theorem rwWall_false_mem_flightLineLeft0_imp_rightEndpoint_of_endpointSep (k : ℤ) (ds ds' : List Bool)
    (hsep : endpointSep k ds ds') {p : V}
    (hpWall : p ∈ rwWall k ds' false) (hpFlight : p ∈ flightLineLeft0 k ds) :
    x p = rwBlockLeft k ds' + rwBlockLen k ds' := by
  -- Unpack the wall equation and combine with the flight-line equation.
  have hyWall : y p = (2 : ℝ) + (rwBlockCenter k ds' - x p) := by
    simpa [rwWall] using hpWall.2
  have hyFlight : y p - x p = (2 : ℝ) + (rwBlockLen k ds) / 2 - rwBlockLeft k ds := hpFlight
  -- Compute `x p` from the two equalities:
  have hxForm :
      x p =
        (rwBlockLeft k ds' + (rwBlockLen k ds') / 2 + rwBlockLeft k ds - (rwBlockLen k ds) / 2) / 2 := by
    have : y p - x p =
        (2 : ℝ) + (rwBlockCenter k ds' - x p) - x p := by
      linarith [hyWall]
    have h2x :
        2 * x p =
          rwBlockCenter k ds' + rwBlockLeft k ds - (rwBlockLen k ds) / 2 := by
      -- equate the two expressions for `y - x` and rearrange
      have : (2 : ℝ) + (rwBlockCenter k ds' - x p) - x p =
          (2 : ℝ) + (rwBlockLen k ds) / 2 - rwBlockLeft k ds := by
        linarith [this, hyFlight]
      linarith [this]
    -- Rewrite `rwBlockCenter = left' + len'/2`.
    have hcenter : rwBlockCenter k ds' = rwBlockLeft k ds' + (rwBlockLen k ds') / 2 := by
      simp [rwBlockCenter]
    have : x p = (rwBlockCenter k ds' + rwBlockLeft k ds - (rwBlockLen k ds) / 2) / 2 := by
      linarith [h2x]
    simpa [hcenter, add_assoc, add_left_comm, add_comm, sub_eq_add_neg] using this
  -- `endpointSep` implies `x p ≥ rightEndpoint(ds')`.
  have hx_ge : x p ≥ rwBlockLeft k ds' + rwBlockLen k ds' := by
    -- Expand and compare against `endpointSep`.
    dsimp [endpointSep] at hsep
    -- Convert `hxForm ≥ right` to the endpoint-separation inequality.
    -- This is a direct linear rewrite.
    have : x p ≥ rwBlockLeft k ds' + rwBlockLen k ds' := by
      -- Use the explicit formula for `x p`.
      -- Multiply by 2 and rearrange.
      nlinarith [hxForm, hsep]
    exact this
  -- But wall membership gives `x p ≤ rightEndpoint(ds')`.
  have hx_le : x p ≤ rwBlockLeft k ds' + rwBlockLen k ds' := hpWall.1.2
  exact le_antisymm hx_le hx_ge

theorem rwWall_false_disjoint_flightLineLeft0_of_endpointSep (k : ℤ) (ds ds' : List Bool)
    (hlen : ds.length = ds'.length) (hsep : endpointSep k ds ds') :
    Disjoint (rwWall k ds' false ∩ {p : V | x p < rwBlockLeft k ds' + rwBlockLen k ds'}) (flightLineLeft0 k ds) := by
  classical
  refine Set.disjoint_left.2 ?_
  intro p hp hpF
  have hpWall : p ∈ rwWall k ds' false := hp.1
  have hx : x p = rwBlockLeft k ds' + rwBlockLen k ds' :=
    rwWall_false_mem_flightLineLeft0_imp_rightEndpoint (k := k) (ds := ds) (ds' := ds') hlen hsep hpWall hpF
  exact (not_lt_of_ge (by simpa [hx] using le_rfl)) hp.2

/-! ## “No spurious collisions” against the whole same-level wall family (ray form) -/

theorem rwBlockLeft_ne_of_length_eq (k : ℤ) {ds ds' : List Bool} (hlen : ds.length = ds'.length) (hne : ds ≠ ds') :
    rwBlockLeft k ds ≠ rwBlockLeft k ds' := by
  -- Separation gives a positive lower bound on the absolute difference.
  have hsep : |rwBlockLeft k ds - rwBlockLeft k ds'| ≥ 2 * rwBlockLen k ds :=
    rwBlockLeft_separated_of_length_eq (k := k) (ds := ds) (ds' := ds') hlen hne
  have hpos : 0 < 2 * rwBlockLen k ds := by
    have : 0 < rwBlockLen k ds := rwBlockLen_pos k ds
    nlinarith
  have : rwBlockLeft k ds - rwBlockLeft k ds' ≠ 0 := by
    -- If the difference were zero, the abs would be zero.
    intro hz
    have : |rwBlockLeft k ds - rwBlockLeft k ds'| = 0 := by simpa [hz]
    exact (not_lt_of_ge hsep) (this ▸ hpos)
  exact sub_ne_zero.1 this

theorem rwWall_false_disjoint_flightRayLeft0_of_ne (k : ℤ) {ds ds' : List Bool}
    (hlen : ds.length = ds'.length) (hne : ds ≠ ds') :
    Disjoint (rwWall k ds' false ∩ {p : V | x p < rwBlockLeft k ds' + rwBlockLen k ds'}) (flightRayLeft0 k ds) := by
  classical
  have hneL : rwBlockLeft k ds ≠ rwBlockLeft k ds' := rwBlockLeft_ne_of_length_eq (k := k) (ds := ds) (ds' := ds') hlen hne
  have hlt : rwBlockLeft k ds' < rwBlockLeft k ds ∨ rwBlockLeft k ds < rwBlockLeft k ds' := lt_or_gt_of_ne hneL.symm
  rcases hlt with hlt | hgt
  · -- Other wall is to the left: use the endpoint separation lemma.
    have hsep : endpointSep k ds ds' :=
      endpointSep_of_length_eq_of_left_gt (k := k) (ds := ds) (ds' := ds') hlen hne (by simpa using hlt)
    -- Disjointness against the full line implies disjointness against the ray subset.
    have hdis :
        Disjoint (rwWall k ds' false ∩ {p : V | x p < rwBlockLeft k ds' + rwBlockLen k ds'}) (flightLineLeft0 k ds) :=
      rwWall_false_disjoint_flightLineLeft0_of_endpointSep (k := k) (ds := ds) (ds' := ds') hlen hsep
    exact hdis.mono_right (flightRayLeft0_subset_flightLineLeft0 (k := k) (ds := ds))
  · -- Other wall is to the right: the ray has `x ≤ left(ds)` so it cannot meet `rwWall ds'`.
    refine Set.disjoint_left.2 ?_
    intro p hpWall hpRay
    have hxRay : x p ≤ rwBlockLeft k ds := hpRay.2
    have hxWall_ge : rwBlockLeft k ds' ≤ x p := hpWall.1.1
    exact (not_lt_of_ge hxRay) (lt_of_lt_of_le hgt hxWall_ge)

end PaperReadWrite

namespace PaperReadWrite

/-! ## The “extremal” flight line (cur=true case; symmetric) -/

/-- The line of slope `-1` passing through the *right endpoint* of `rwWall k ds true`. -/
def flightLineRight1 (k : ℤ) (ds : List Bool) : Set V :=
  { p | y p + x p = (2 : ℝ) + (rwBlockLen k ds) / 2 + (rwBlockLeft k ds + rwBlockLen k ds) }

theorem mem_flightLineRight1_iff (k : ℤ) (ds : List Bool) (p : V) :
    p ∈ flightLineRight1 k ds ↔
      y p + x p = (2 : ℝ) + (rwBlockLen k ds) / 2 + (rwBlockLeft k ds + rwBlockLen k ds) := Iff.rfl

/-- The ray starting at the right endpoint directionally moving down-right: the `flightLineRight1`
equation plus the monotonicity constraint `rwBlockLeft+len ≤ x`. -/
def flightRayRight1 (k : ℤ) (ds : List Bool) : Set V :=
  flightLineRight1 k ds ∩ { p | rwBlockLeft k ds + rwBlockLen k ds ≤ x p }

theorem flightRayRight1_subset_flightLineRight1 (k : ℤ) (ds : List Bool) :
    flightRayRight1 k ds ⊆ flightLineRight1 k ds := by
  intro p hp
  exact hp.1

theorem rwWall_true_mem_flightLineRight1_imp_leftEndpoint (k : ℤ) (ds ds' : List Bool)
    (hlen : ds.length = ds'.length) (hsep : endpointSep k ds' ds) {p : V}
    (hpWall : p ∈ rwWall k ds' true) (hpFlight : p ∈ flightLineRight1 k ds) :
    x p = rwBlockLeft k ds' := by
  -- Unpack the wall equation and combine with the flight-line equation.
  have hyWall : y p = (2 : ℝ) + (-rwBlockCenter k ds' + x p) := by
    simpa [rwWall] using hpWall.2
  have hyFlight : y p + x p =
      (2 : ℝ) + (rwBlockLen k ds) / 2 + (rwBlockLeft k ds + rwBlockLen k ds) := hpFlight
  -- Compute `x p` from the two equalities.
  have hxEq :
      2 * x p = rwBlockCenter k ds' + rwBlockLeft k ds + (3 / 2 : ℝ) * rwBlockLen k ds := by
    have : (2 : ℝ) + (-rwBlockCenter k ds' + x p) + x p =
        (2 : ℝ) + (rwBlockLen k ds) / 2 + (rwBlockLeft k ds + rwBlockLen k ds) := by
      have : y p + x p = (2 : ℝ) + (-rwBlockCenter k ds' + x p) + x p := by
        linarith [hyWall]
      linarith [this, hyFlight]
    linarith [this]
  have hlenLen : rwBlockLen k ds' = rwBlockLen k ds :=
    rwBlockLen_eq_of_length_eq (k := k) (ds := ds') (ds' := ds) hlen.symm
  have hcenter : rwBlockCenter k ds' = rwBlockLeft k ds' + (rwBlockLen k ds) / 2 := by
    simp [rwBlockCenter, hlenLen]
  have hxForm : x p = (rwBlockLeft k ds + rwBlockLeft k ds') / 2 + rwBlockLen k ds := by
    have : x p =
        (rwBlockCenter k ds' + rwBlockLeft k ds + (3 / 2 : ℝ) * rwBlockLen k ds) / 2 := by
      linarith [hxEq]
    -- Substitute `rwBlockCenter = left' + len/2`.
    -- `(left' + len/2 + left + 3/2 len)/2 = (left+left')/2 + len`.
    simpa [hcenter, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using this
  -- Use the `endpointSep` inequality to show `x p ≤ left'`.
  have hgap : rwBlockLeft k ds' - (rwBlockLeft k ds + rwBlockLen k ds) ≥ rwBlockLen k ds := by
    -- `endpointSep k ds' ds` plus equal lengths implies a `2*len` separation to the right.
    dsimp [endpointSep] at hsep
    have : rwBlockLeft k ds' - (rwBlockLeft k ds + rwBlockLen k ds) ≥ rwBlockLen k ds := by
      -- RHS becomes `len/2 + len/2 = len`.
      nlinarith [hsep, hlenLen]
    exact this
  have hx_le : x p ≤ rwBlockLeft k ds' := by
    -- From `hxForm` and `hgap` (which implies `left' ≥ left + 2*len`).
    have hsep2 : rwBlockLeft k ds' ≥ rwBlockLeft k ds + 2 * rwBlockLen k ds := by
      nlinarith [hgap]
    have : (rwBlockLeft k ds + rwBlockLeft k ds') / 2 + rwBlockLen k ds ≤ rwBlockLeft k ds' := by
      nlinarith [hsep2]
    simpa [hxForm] using this
  -- Wall membership gives `left' ≤ x p`.
  have hx_ge : rwBlockLeft k ds' ≤ x p := hpWall.1.1
  exact le_antisymm hx_le hx_ge

/-- A length-free version of `rwWall_true_mem_flightLineRight1_imp_leftEndpoint`:
the endpoint-separation inequality alone forces the intersection to occur at the **left endpoint**
of the (potentially different-length) wall segment. -/
theorem rwWall_true_mem_flightLineRight1_imp_leftEndpoint_of_endpointSep (k : ℤ) (ds ds' : List Bool)
    (hsep : endpointSep k ds' ds) {p : V}
    (hpWall : p ∈ rwWall k ds' true) (hpFlight : p ∈ flightLineRight1 k ds) :
    x p = rwBlockLeft k ds' := by
  have hyWall : y p = (2 : ℝ) + (-rwBlockCenter k ds' + x p) := by
    simpa [rwWall] using hpWall.2
  have hyFlight : y p + x p =
      (2 : ℝ) + (rwBlockLen k ds) / 2 + (rwBlockLeft k ds + rwBlockLen k ds) := hpFlight
  -- Solve for `x p`.
  have hxForm :
      x p =
        (rwBlockLeft k ds + rwBlockLen k ds + rwBlockLeft k ds' + (rwBlockLen k ds') / 2 + (rwBlockLen k ds) / 2) / 2 := by
    have : y p + x p = (2 : ℝ) + (-rwBlockCenter k ds' + x p) + x p := by
      linarith [hyWall]
    have h2x :
        2 * x p =
          rwBlockCenter k ds' + rwBlockLeft k ds + (3 / 2 : ℝ) * rwBlockLen k ds := by
      have : (2 : ℝ) + (-rwBlockCenter k ds' + x p) + x p =
          (2 : ℝ) + (rwBlockLen k ds) / 2 + (rwBlockLeft k ds + rwBlockLen k ds) := by
        linarith [this, hyFlight]
      linarith [this]
    have hcenter : rwBlockCenter k ds' = rwBlockLeft k ds' + (rwBlockLen k ds') / 2 := by
      simp [rwBlockCenter]
    have : x p =
        (rwBlockCenter k ds' + rwBlockLeft k ds + (3 / 2 : ℝ) * rwBlockLen k ds) / 2 := by
      linarith [h2x]
    -- Normalize to a symmetric “endpoint” expression.
    -- `(left' + len'/2 + left + 3/2 len)/2 = (left+len) + (left' - (left+len) + len/2 + len'/2)/2`.
    -- Keep it in a form suitable for `nlinarith` with `endpointSep`.
    simpa [hcenter, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using this
  -- `endpointSep` implies `x p ≤ leftEndpoint(ds')`.
  have hx_le : x p ≤ rwBlockLeft k ds' := by
    dsimp [endpointSep] at hsep
    nlinarith [hxForm, hsep]
  -- Wall membership gives `left' ≤ x p`.
  have hx_ge : rwBlockLeft k ds' ≤ x p := hpWall.1.1
  exact le_antisymm hx_le hx_ge

theorem rwWall_true_disjoint_flightLineRight1_of_endpointSep (k : ℤ) (ds ds' : List Bool)
    (hlen : ds.length = ds'.length) (hsep : endpointSep k ds' ds) :
    Disjoint (rwWall k ds' true ∩ {p : V | rwBlockLeft k ds' < x p}) (flightLineRight1 k ds) := by
  classical
  refine Set.disjoint_left.2 ?_
  intro p hp hpF
  have hpWall : p ∈ rwWall k ds' true := hp.1
  have hx : x p = rwBlockLeft k ds' :=
    rwWall_true_mem_flightLineRight1_imp_leftEndpoint (k := k) (ds := ds) (ds' := ds') hlen hsep hpWall hpF
  exact (not_lt_of_eq hx) hp.2

theorem rwWall_true_disjoint_flightRayRight1_of_ne (k : ℤ) {ds ds' : List Bool}
    (hlen : ds.length = ds'.length) (hne : ds ≠ ds') :
    Disjoint (rwWall k ds' true ∩ {p : V | rwBlockLeft k ds' < x p}) (flightRayRight1 k ds) := by
  classical
  have hneL : rwBlockLeft k ds ≠ rwBlockLeft k ds' :=
    rwBlockLeft_ne_of_length_eq (k := k) (ds := ds) (ds' := ds') hlen hne
  have hlt : rwBlockLeft k ds' < rwBlockLeft k ds ∨ rwBlockLeft k ds < rwBlockLeft k ds' :=
    lt_or_gt_of_ne hneL.symm
  rcases hlt with hlt | hgt
  · -- Other wall is to the left: the ray has `x ≥ right(ds)` so it cannot meet `rwWall ds'`.
    refine Set.disjoint_left.2 ?_
    intro p hpWall hpRay
    have hxRay : rwBlockLeft k ds + rwBlockLen k ds ≤ x p := hpRay.2
    have hxWall_le : x p ≤ rwBlockLeft k ds' + rwBlockLen k ds' := hpWall.1.1.2
    have hlenLen : rwBlockLen k ds' = rwBlockLen k ds :=
      rwBlockLen_eq_of_length_eq (k := k) (ds := ds') (ds' := ds) hlen.symm
    -- Since `ds'` is strictly left of `ds`, its right endpoint is left of `right(ds)`.
    have : rwBlockLeft k ds' + rwBlockLen k ds' < rwBlockLeft k ds + rwBlockLen k ds := by
      nlinarith [hlt, hlenLen]
    exact (not_lt_of_ge hxRay) (lt_of_le_of_lt hxWall_le this)
  · -- Other wall is to the right: use the endpoint-separation inequality (swapped).
    have hsep : endpointSep k ds' ds :=
      endpointSep_of_length_eq_of_left_gt (k := k) (ds := ds') (ds' := ds) hlen.symm hne.symm (by simpa using hgt)
    have hdis :
        Disjoint (rwWall k ds' true ∩ {p : V | rwBlockLeft k ds' < x p}) (flightLineRight1 k ds) :=
      rwWall_true_disjoint_flightLineRight1_of_endpointSep (k := k) (ds := ds) (ds' := ds') hlen hsep
    exact hdis.mono_right (flightRayRight1_subset_flightLineRight1 (k := k) (ds := ds))

/-
## Easy cross-`k` exclusions (partial “no spurious collisions” scaffolding)

For the straight read-only walls, all `x`-domains lie inside `headInterval k ⊆ [0,1]`.
The extremal rays `flightRayLeft0` / `flightRayRight1` impose a one-sided `x`-inequality, so they
cannot collide with any wall family whose head interval lies strictly on the other side.

These lemmas only handle the “wrong side of the head index ordering” case; the remaining
`k' < k` (resp. `k < k'`) cases require the Appendix-style quantitative inequalities and are part
of the still-open WS7.3 corridor/trajectory proof.
-/

theorem rwWall_disjoint_flightRayLeft0_of_k_lt (k k' : ℤ) (ds ds' : List Bool) (cur' : Bool)
    (hkk' : k < k') :
    Disjoint (rwWall k' ds' cur') (flightRayLeft0 k ds) := by
  classical
  refine Set.disjoint_left.2 ?_
  intro p hpWall hpRay
  have hxRay : x p ≤ rwBlockLeft k ds := hpRay.2
  -- `x p` lies in `headInterval k'`, hence `headLeft k' ≤ x p`.
  have hxHead' : x p ∈ headInterval k' :=
    (rwBlockInterval_subset_headInterval (k := k') (ds := ds')) hpWall.1
  have hx_ge : headLeft k' ≤ x p := hxHead'.1
  -- `rwBlockLeft k ds` lies in `headInterval k`, hence `rwBlockLeft ≤ headRight k`.
  have hleftHead : rwBlockLeft k ds ∈ headInterval k := by
    have hx01 : cantorLeft ds ∈ Set.Icc (0 : ℝ) 1 := ⟨cantorLeft_nonneg ds, cantorLeft_le_one ds⟩
    simpa [rwBlockLeft] using (tau_mem_headInterval (k := k) (x := cantorLeft ds) hx01)
  have hleft_le : rwBlockLeft k ds ≤ headRight k := hleftHead.2
  have hsep : headRight k < headLeft k' := headRight_lt_headLeft_of_lt hkk'
  have hx_gt : rwBlockLeft k ds < x p := lt_of_le_of_lt hleft_le (lt_of_lt_of_le hsep hx_ge)
  exact (not_lt_of_ge hxRay) hx_gt

theorem rwWall_disjoint_flightRayRight1_of_k_gt (k k' : ℤ) (ds ds' : List Bool) (cur' : Bool)
    (hkk' : k' < k) :
    Disjoint (rwWall k' ds' cur') (flightRayRight1 k ds) := by
  classical
  refine Set.disjoint_left.2 ?_
  intro p hpWall hpRay
  have hxRay : rwBlockLeft k ds + rwBlockLen k ds ≤ x p := hpRay.2
  -- `x p` lies in `headInterval k'`, hence `x p ≤ headRight k'`.
  have hxHead' : x p ∈ headInterval k' :=
    (rwBlockInterval_subset_headInterval (k := k') (ds := ds')) hpWall.1
  have hx_le' : x p ≤ headRight k' := hxHead'.2
  -- The right endpoint of the `k`-block lies in `headInterval k`, hence `headLeft k ≤ rightEndpoint`.
  have hrHead : (rwBlockLeft k ds + rwBlockLen k ds) ∈ headInterval k := by
    -- Right endpoint corresponds to `tau k (cantorLeft ds + cantorWidth ds)`.
    have hx01 : (cantorLeft ds + cantorWidth ds) ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨?_, ?_⟩
      · have h0 : 0 ≤ cantorLeft ds := cantorLeft_nonneg ds
        have h1 : 0 ≤ cantorWidth ds := by
          unfold cantorWidth
          have : 0 < (3 : ℝ) ^ ds.length := by positivity
          exact le_of_lt (inv_pos.2 this)
        linarith
      · exact cantorLeft_add_width_le_one ds
    have ht : tau k (cantorLeft ds + cantorWidth ds) = rwBlockLeft k ds + rwBlockLen k ds := by
      simp [rwBlockLeft, rwBlockLen, tau_eq_affine, cantorWidth, mul_add, add_assoc, add_left_comm, add_comm]
    simpa [headInterval] using (ht ▸ tau_mem_headInterval (k := k) (x := cantorLeft ds + cantorWidth ds) hx01)
  have hr_ge : headLeft k ≤ rwBlockLeft k ds + rwBlockLen k ds := hrHead.1
  have hsep : headRight k' < headLeft k := headRight_lt_headLeft_of_lt hkk'
  have hx_lt : x p < rwBlockLeft k ds + rwBlockLen k ds := lt_of_le_of_lt hx_le' (lt_of_lt_of_le hsep hr_ge)
  exact (not_lt_of_ge hxRay) hx_lt

/-!
## Easy cross-`k` exclusions for rewrite walls

The perturbed-slope walls `rwWallRewrite` share the same `x`-domains `rwBlockInterval k ds` as
`rwWall`, so the simple head-interval arguments apply unchanged.
-/

theorem rwWallRewrite_disjoint_flightRayLeft0_of_k_lt (k k' : ℤ) (ds ds' : List Bool) (cur' : Bool)
    (hkk' : k < k') :
    Disjoint (rwWallRewrite k' ds' cur') (flightRayLeft0 k ds) := by
  classical
  refine Set.disjoint_left.2 ?_
  intro p hpWall hpRay
  have hxRay : x p ≤ rwBlockLeft k ds := hpRay.2
  -- `x p` lies in `headInterval k'`, hence `headLeft k' ≤ x p`.
  have hxHead' : x p ∈ headInterval k' :=
    (rwBlockInterval_subset_headInterval (k := k') (ds := ds')) hpWall.1
  have hx_ge : headLeft k' ≤ x p := hxHead'.1
  -- `rwBlockLeft k ds` lies in `headInterval k`, hence `rwBlockLeft ≤ headRight k`.
  have hleftHead : rwBlockLeft k ds ∈ headInterval k := by
    have hx01 : cantorLeft ds ∈ Set.Icc (0 : ℝ) 1 := ⟨cantorLeft_nonneg ds, cantorLeft_le_one ds⟩
    simpa [rwBlockLeft] using (tau_mem_headInterval (k := k) (x := cantorLeft ds) hx01)
  have hleft_le : rwBlockLeft k ds ≤ headRight k := hleftHead.2
  have hsep : headRight k < headLeft k' := headRight_lt_headLeft_of_lt hkk'
  have hx_gt : rwBlockLeft k ds < x p := lt_of_le_of_lt hleft_le (lt_of_lt_of_le hsep hx_ge)
  exact (not_lt_of_ge hxRay) hx_gt

theorem rwWallRewrite_disjoint_flightRayRight1_of_k_gt (k k' : ℤ) (ds ds' : List Bool) (cur' : Bool)
    (hkk' : k' < k) :
    Disjoint (rwWallRewrite k' ds' cur') (flightRayRight1 k ds) := by
  classical
  refine Set.disjoint_left.2 ?_
  intro p hpWall hpRay
  have hxRay : rwBlockLeft k ds + rwBlockLen k ds ≤ x p := hpRay.2
  -- `x p` lies in `headInterval k'`, hence `x p ≤ headRight k'`.
  have hxHead' : x p ∈ headInterval k' :=
    (rwBlockInterval_subset_headInterval (k := k') (ds := ds')) hpWall.1
  have hx_le' : x p ≤ headRight k' := hxHead'.2
  -- The right endpoint of the `k`-block lies in `headInterval k`, hence `headLeft k ≤ rightEndpoint`.
  have hrHead : (rwBlockLeft k ds + rwBlockLen k ds) ∈ headInterval k := by
    have hx01 : (cantorLeft ds + cantorWidth ds) ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨?_, cantorLeft_add_width_le_one ds⟩
      have h0 : 0 ≤ cantorLeft ds := cantorLeft_nonneg ds
      have h1 : 0 ≤ cantorWidth ds := by
        unfold cantorWidth
        have : 0 < (3 : ℝ) ^ ds.length := by positivity
        exact le_of_lt (inv_pos.2 this)
      linarith
    have ht : tau k (cantorLeft ds + cantorWidth ds) = rwBlockLeft k ds + rwBlockLen k ds := by
      simp [rwBlockLeft, rwBlockLen, tau_eq_affine, cantorWidth, mul_add, add_assoc, add_left_comm, add_comm]
    simpa [headInterval] using (ht ▸ tau_mem_headInterval (k := k) (x := cantorLeft ds + cantorWidth ds) hx01)
  have hr_ge : headLeft k ≤ rwBlockLeft k ds + rwBlockLen k ds := hrHead.1
  have hsep : headRight k' < headLeft k := headRight_lt_headLeft_of_lt hkk'
  have hx_lt : x p < rwBlockLeft k ds + rwBlockLen k ds := lt_of_le_of_lt hx_le' (lt_of_lt_of_le hsep hr_ge)
  exact (not_lt_of_ge hxRay) hx_lt

/-!
## Same-`k`, same-block exclusions for rewrite walls against the read-only extremal rays

In the paper, the “symbol change” walls descend more slowly (`rewriteSlope < 1`), while the
read-only extremal rays are on a fixed slope `±1`. As a consequence, even **within the same block**
(`k, ds` fixed), the extremal ray cannot meet the rewrite wall segment: the ray forces an endpoint
`x`-value, but the rewrite wall is strictly below the corresponding read-only endpoint height.

These lemmas are a small mechanizable bridge toward the paper’s statement that collision avoidance
is “easier” in the rewrite case.
-/

private theorem rewriteSlope_lt_one (k : ℤ) (ds : List Bool) : rewriteSlope k ds < 1 := by
  have hlen : 0 < rwBlockLen k ds := rwBlockLen_pos k ds
  have hden : (1 : ℝ) < 1 + rwBlockLen k ds := by linarith
  -- Use the standard inequality: `1/(1+a) < 1` for `a > 0`.
  simpa [rewriteSlope] using (one_div_lt_one (by linarith) |>.2 hden)

theorem rwWallRewrite_false_disjoint_flightRayLeft0_self (k : ℤ) (ds : List Bool) :
    Disjoint (rwWallRewrite k ds false) (flightRayLeft0 k ds) := by
  classical
  refine Set.disjoint_left.2 ?_
  intro p hpWall hpRay
  have hxWallL : rwBlockLeft k ds ≤ x p := hpWall.1.1
  have hxRayU : x p ≤ rwBlockLeft k ds := hpRay.2
  have hx : x p = rwBlockLeft k ds := le_antisymm hxRayU hxWallL
  -- Compare the `y`-value forced by the flight line with the rewrite-wall endpoint value.
  have hyRay : y p = (2 : ℝ) + (rwBlockLen k ds) / 2 := by
    have hline : p ∈ flightLineLeft0 k ds := (flightRayLeft0_subset_flightLineLeft0 (k := k) (ds := ds)) hpRay
    have : y p - x p = (2 : ℝ) + (rwBlockLen k ds) / 2 - rwBlockLeft k ds :=
      (mem_flightLineLeft0_iff (k := k) (ds := ds) (p := p)).1 hline
    -- Substitute `x = left`.
    nlinarith [this, hx]
  have hyWall : y p = (2 : ℝ) + rewriteSlope k ds * ((rwBlockLen k ds) / 2) := by
    -- At the left endpoint `x=left`, `center - x = len/2`.
    have : rwBlockCenter k ds - x p = (rwBlockLen k ds) / 2 := by
      simp [rwBlockCenter, hx]
    -- Unfold the wall equation.
    have hyEq : y p =
        (2 : ℝ) + (rewriteSlope k ds) * (rwBlockCenter k ds - x p) := by
      simpa [rwWallRewrite] using hpWall.2
    simpa [this] using hyEq
  have hlenPos : 0 < rwBlockLen k ds := rwBlockLen_pos k ds
  have hm1 : rewriteSlope k ds < 1 := rewriteSlope_lt_one k ds
  -- Contradiction: `m*len/2 < len/2`.
  have : (2 : ℝ) + rewriteSlope k ds * ((rwBlockLen k ds) / 2) < (2 : ℝ) + (rwBlockLen k ds) / 2 := by
    have : rewriteSlope k ds * ((rwBlockLen k ds) / 2) < 1 * ((rwBlockLen k ds) / 2) := by
      have hhalf : 0 < (rwBlockLen k ds) / 2 := by nlinarith [hlenPos]
      simpa [one_mul] using (mul_lt_mul_of_pos_right hm1 hhalf)
    linarith
  exact (ne_of_lt this) (hyWall.trans hyRay.symm)

theorem rwWallRewrite_true_disjoint_flightRayRight1_self (k : ℤ) (ds : List Bool) :
    Disjoint (rwWallRewrite k ds true) (flightRayRight1 k ds) := by
  classical
  refine Set.disjoint_left.2 ?_
  intro p hpWall hpRay
  have hxWallU : x p ≤ rwBlockLeft k ds + rwBlockLen k ds := hpWall.1.2
  have hxRayL : rwBlockLeft k ds + rwBlockLen k ds ≤ x p := hpRay.2
  have hx : x p = rwBlockLeft k ds + rwBlockLen k ds := le_antisymm hxWallU hxRayL
  have hyRay : y p = (2 : ℝ) + (rwBlockLen k ds) / 2 := by
    have hline : p ∈ flightLineRight1 k ds := (flightRayRight1_subset_flightLineRight1 (k := k) (ds := ds)) hpRay
    have : y p + x p =
        (2 : ℝ) + (rwBlockLen k ds) / 2 + (rwBlockLeft k ds + rwBlockLen k ds) :=
      (mem_flightLineRight1_iff (k := k) (ds := ds) (p := p)).1 hline
    nlinarith [this, hx]
  have hyWall : y p = (2 : ℝ) + rewriteSlope k ds * ((rwBlockLen k ds) / 2) := by
    -- At the right endpoint `x=left+len`, `x - center = len/2`.
    have : x p - rwBlockCenter k ds = (rwBlockLen k ds) / 2 := by
      simp [rwBlockCenter, hx]
    have hyEq : y p =
        (2 : ℝ) + (rewriteSlope k ds) * (-rwBlockCenter k ds + x p) := by
      simpa [rwWallRewrite] using hpWall.2
    -- `-center + x = x - center`.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, this] using hyEq
  have hlenPos : 0 < rwBlockLen k ds := rwBlockLen_pos k ds
  have hm1 : rewriteSlope k ds < 1 := rewriteSlope_lt_one k ds
  have : (2 : ℝ) + rewriteSlope k ds * ((rwBlockLen k ds) / 2) < (2 : ℝ) + (rwBlockLen k ds) / 2 := by
    have : rewriteSlope k ds * ((rwBlockLen k ds) / 2) < 1 * ((rwBlockLen k ds) / 2) := by
      have hhalf : 0 < (rwBlockLen k ds) / 2 := by nlinarith [hlenPos]
      simpa [one_mul] using (mul_lt_mul_of_pos_right hm1 hhalf)
    linarith
  exact (ne_of_lt this) (hyWall.trans hyRay.symm)

end PaperReadWrite

end Billiards
end MirandaDynamics
end HeytingLean
