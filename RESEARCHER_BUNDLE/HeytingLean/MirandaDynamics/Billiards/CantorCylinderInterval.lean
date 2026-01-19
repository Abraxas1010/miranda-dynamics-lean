import HeytingLean.MirandaDynamics.Billiards.CantorCylinders

/-!
# MirandaDynamics.Billiards: Cantor cylinders as explicit intervals

The paper’s billiard-wall formulas (Appendix of arXiv:2512.19156) refer to explicit Cantor blocks
as *intervals* with computable left endpoints and lengths.

`CantorCylinders.lean` already defines the cylinder set `cantorCylinder ds` via the digit-splitting
recursion. This file proves that each such cylinder is exactly a closed interval.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set

/-! ## Left endpoints and widths -/

/-- The width of a length-`n` Cantor cylinder: `3^{-n}`. -/
noncomputable def cantorWidth (ds : List Bool) : ℝ :=
  ((3 : ℝ) ^ ds.length)⁻¹

@[simp] theorem cantorWidth_nil : cantorWidth ([] : List Bool) = (1 : ℝ) := by
  simp [cantorWidth]

@[simp] theorem cantorWidth_cons (b : Bool) (ds : List Bool) :
    cantorWidth (b :: ds) = (oneThird : ℝ) * cantorWidth ds := by
  -- `3^{-(n+1)} = (1/3) * 3^{-n}`.
  simp [cantorWidth, oneThird, pow_succ, mul_assoc, inv_mul_eq_iff_eq_mul, mul_comm, mul_left_comm]

/-- The left endpoint of the Cantor cylinder determined by a finite digit list `ds`.

Digits are in `{0,2}` (represented as `Bool`), so the left endpoint is the base-3 expansion with
digits `0`/`2` followed by zeros. -/
noncomputable def cantorLeft : List Bool → ℝ
  | [] => 0
  | b :: ds =>
      (if b then twoThird else 0) + (oneThird : ℝ) * cantorLeft ds

@[simp] theorem cantorLeft_nil : cantorLeft ([] : List Bool) = (0 : ℝ) := rfl

@[simp] theorem cantorLeft_cons (b : Bool) (ds : List Bool) :
    cantorLeft (b :: ds) = (if b then twoThird else 0) + (oneThird : ℝ) * cantorLeft ds := rfl

theorem cantorLeft_nonneg : ∀ ds : List Bool, 0 ≤ cantorLeft ds := by
  intro ds
  induction ds with
  | nil =>
      simp [cantorLeft]
  | cons b ds ih =>
      cases b <;> simp [cantorLeft, twoThird, oneThird, ih] <;> nlinarith

theorem cantorLeft_add_width_le_one : ∀ ds : List Bool, cantorLeft ds + cantorWidth ds ≤ (1 : ℝ) := by
  intro ds
  induction ds with
  | nil =>
      simp [cantorLeft, cantorWidth]
  | cons b ds ih =>
      cases b with
      | false =>
          -- left = (1/3)*left', width = (1/3)*width'
          have := ih
          -- Divide the whole inequality by 3 (positive).
          have hdiv : (cantorLeft ds + cantorWidth ds) / 3 ≤ (1 : ℝ) / 3 := by
            nlinarith
          -- Rewrite `left + width` for the cons case.
          simpa [cantorLeft, cantorWidth_cons, add_assoc, add_left_comm, add_comm, oneThird, div_eq_mul_inv,
            mul_add] using hdiv
      | true =>
          -- left = 2/3 + (1/3)*left', width = (1/3)*width'
          have := ih
          have hdiv : (cantorLeft ds + cantorWidth ds) / 3 ≤ (1 : ℝ) / 3 := by
            nlinarith
          -- `2/3 + (left+width)/3 ≤ 1` since `left+width ≤ 1`.
          have : (twoThird : ℝ) + (cantorLeft ds + cantorWidth ds) / 3 ≤ 1 := by
            -- Use `hdiv` and `twoThird + 1/3 = 1`.
            have h23 : (twoThird : ℝ) + (1 : ℝ) / 3 = 1 := by
              simp [twoThird, oneThird, div_eq_mul_inv]
              ring_nf
            have : (twoThird : ℝ) + (cantorLeft ds + cantorWidth ds) / 3 ≤ (twoThird : ℝ) + (1 : ℝ) / 3 :=
              add_le_add_left hdiv (twoThird : ℝ)
            simpa [h23] using this
          -- Rewrite `cantorLeft (true::ds) + cantorWidth (true::ds)`.
          simpa [cantorLeft, cantorWidth_cons, oneThird, div_eq_mul_inv, mul_add, add_assoc, add_left_comm,
            add_comm] using this

theorem cantorLeft_le_one (ds : List Bool) : cantorLeft ds ≤ (1 : ℝ) := by
  have h := cantorLeft_add_width_le_one ds
  have hw : 0 ≤ cantorWidth ds := by
    unfold cantorWidth
    have : 0 < (3 : ℝ) ^ ds.length := by positivity
    exact le_of_lt (inv_pos.2 this)
  exact le_trans (le_add_of_nonneg_right hw) h

theorem cantorWidth_le_one (ds : List Bool) : cantorWidth ds ≤ (1 : ℝ) := by
  unfold cantorWidth
  have hpow : (1 : ℝ) ≤ (3 : ℝ) ^ ds.length := by
    simpa using (one_le_pow_of_one_le (by linarith : (1 : ℝ) ≤ 3) (Nat.zero_le ds.length))
  have hpos : 0 < (3 : ℝ) ^ ds.length := by positivity
  -- invert `1 ≤ 3^n` to get `1/(3^n) ≤ 1`.
  have : ((3 : ℝ) ^ ds.length)⁻¹ ≤ (1 : ℝ)⁻¹ := inv_le_inv_of_le hpos hpow
  simpa using this

theorem abs_cantorLeft_sub_le_one_sub_width (ds ds' : List Bool) (hlen : ds.length = ds'.length) :
    |cantorLeft ds - cantorLeft ds'| ≤ (1 : ℝ) - cantorWidth ds := by
  have hds0 : 0 ≤ cantorLeft ds := cantorLeft_nonneg ds
  have hds1 : cantorLeft ds ≤ 1 - cantorWidth ds := by
    have := cantorLeft_add_width_le_one ds
    linarith
  have hwidth : cantorWidth ds' = cantorWidth ds := by
    simp [cantorWidth, hlen]
  have hds'0 : 0 ≤ cantorLeft ds' := cantorLeft_nonneg ds'
  have hds'1 : cantorLeft ds' ≤ 1 - cantorWidth ds := by
    have := cantorLeft_add_width_le_one ds'
    -- rewrite the width of `ds'` using the common length.
    simpa [hwidth] using (by linarith)
  -- Both values lie in `[0, 1 - width]`.
  have h1 : cantorLeft ds - cantorLeft ds' ≤ 1 - cantorWidth ds := by linarith
  have h2 : -(1 - cantorWidth ds) ≤ cantorLeft ds - cantorLeft ds' := by linarith
  exact abs_le.2 ⟨h2, h1⟩

/-!
## Quantitative separation of cylinder left endpoints

For two distinct digit lists of the same length, the associated left endpoints differ by at least
`2 * cantorWidth` (this is the `0/2`-digit Cantor gap size).
-/

theorem cantorLeft_separated_of_length_eq {ds ds' : List Bool} (hlen : ds.length = ds'.length) (hne : ds ≠ ds') :
    |cantorLeft ds - cantorLeft ds'| ≥ 2 * cantorWidth ds := by
  -- Induct on `ds`; use `hlen` to split `ds'` in lockstep.
  induction ds generalizing ds' with
  | nil =>
      cases ds' with
      | nil => cases hne rfl
      | cons b ds' => simp at hlen
  | cons b ds ih =>
      cases ds' with
      | nil => simp at hlen
      | cons b' ds' =>
          have hlen' : ds.length = ds'.length := by simpa using Nat.succ.inj hlen
          by_cases hb : b = b'
          · subst hb
            have hne' : ds ≠ ds' := by
              intro hEq
              apply hne
              simp [hEq]
            have htail : |cantorLeft ds - cantorLeft ds'| ≥ 2 * cantorWidth ds :=
              ih (ds' := ds') hlen' hne'
            have hc : (0 : ℝ) ≤ (oneThird : ℝ) := by
              simp [oneThird]
              positivity
            -- Scale both sides by `1/3` and rewrite.
            have := mul_le_mul_of_nonneg_left htail hc
            -- `|(1/3)*(a-b)| = (1/3)*|a-b|` for `1/3 ≥ 0`.
            simpa [cantorLeft, cantorWidth_cons, oneThird, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm,
              abs_mul, abs_of_nonneg hc] using this
          · -- Leading digits differ: the head contributes a `2/3` gap.
            let A : ℝ := (if b then twoThird else 0) - (if b' then twoThird else 0)
            let B : ℝ := (oneThird : ℝ) * (cantorLeft ds - cantorLeft ds')
            have hA : |A| = (twoThird : ℝ) := by
              cases b <;> cases b' <;> simp [A, hb, twoThird]
            have hB : |B| ≤ (oneThird : ℝ) * ((1 : ℝ) - cantorWidth ds) := by
              have hc : 0 ≤ (oneThird : ℝ) := by
                simp [oneThird]
                positivity
              have h0 := abs_cantorLeft_sub_le_one_sub_width ds ds' hlen'
              have := mul_le_mul_of_nonneg_left h0 hc
              simpa [B, abs_mul, abs_of_nonneg hc, mul_assoc, mul_left_comm, mul_comm] using this
            have hAB : |A + B| ≥ (twoThird : ℝ) - (oneThird : ℝ) * ((1 : ℝ) - cantorWidth ds) := by
              -- `|A + B| ≥ |A| - |B|`.
              have := abs_add_ge_abs_sub_abs A B
              have : |A + B| ≥ |A| - |B| := by simpa [sub_eq_add_neg] using this
              have : |A| - |B| ≥ (twoThird : ℝ) - (oneThird : ℝ) * ((1 : ℝ) - cantorWidth ds) := by
                nlinarith [hA, hB]
              exact le_trans this
            -- Compare this lower bound with `2 * cantorWidth (b::ds) = (2/3)*cantorWidth ds`.
            have hwidth : 2 * cantorWidth (b :: ds) = (twoThird : ℝ) * cantorWidth ds := by
              simp [cantorWidth_cons, twoThird, oneThird, mul_assoc, mul_left_comm, mul_comm]
              ring_nf
            have hwle : cantorWidth ds ≤ (1 : ℝ) := cantorWidth_le_one ds
            have hfinal :
                (twoThird : ℝ) - (oneThird : ℝ) * ((1 : ℝ) - cantorWidth ds) ≥ (twoThird : ℝ) * cantorWidth ds := by
              -- Algebra: `2/3 - (1/3)(1-w) = (1+w)/3 ≥ (2/3)w` since `w ≤ 1`.
              nlinarith [hwle, twoThird, oneThird]
            -- Finish by rewriting `A+B` as the `cantorLeft` difference.
            have hrewrite :
                A + B = cantorLeft (b :: ds) - cantorLeft (b' :: ds') := by
              simp [A, B, cantorLeft, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul,
                mul_assoc, mul_left_comm, mul_comm]
            have : |cantorLeft (b :: ds) - cantorLeft (b' :: ds')| ≥ (twoThird : ℝ) * cantorWidth ds := by
              simpa [hrewrite] using le_trans hfinal hAB
            simpa [hwidth] using this

/-!
### Append-singleton identities

These are convenient for the Appendix-style “fixed last digit” separation estimates: when two
digit lists differ only in their *prefix* (the last digit is fixed), their left-endpoint separation
is controlled by the prefix width rather than the full-cylinder width.
-/

theorem cantorLeft_append_singleton (ds : List Bool) (b : Bool) :
    cantorLeft (ds ++ [b]) = cantorLeft ds + cantorWidth ds * (if b then twoThird else 0) := by
  induction ds with
  | nil =>
      cases b <;> simp [cantorLeft, cantorWidth]
  | cons a ds ih =>
      simp [cantorLeft, cantorWidth_cons, ih, mul_add, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
        mul_comm]

theorem cantorLeft_sub_append_singleton (ds ds' : List Bool) (b : Bool) (hlen : ds.length = ds'.length) :
    cantorLeft (ds ++ [b]) - cantorLeft (ds' ++ [b]) = cantorLeft ds - cantorLeft ds' := by
  have hw : cantorWidth ds = cantorWidth ds' := by simp [cantorWidth, hlen]
  simp [cantorLeft_append_singleton, hw, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add]

theorem cantorLeft_separated_append_singleton_of_length_eq {ds ds' : List Bool}
    (hlen : ds.length = ds'.length) (hne : ds ≠ ds') (b : Bool) :
    |cantorLeft (ds ++ [b]) - cantorLeft (ds' ++ [b])| ≥ 2 * cantorWidth ds := by
  have hsub :
      cantorLeft (ds ++ [b]) - cantorLeft (ds' ++ [b]) = cantorLeft ds - cantorLeft ds' :=
    cantorLeft_sub_append_singleton (ds := ds) (ds' := ds') (b := b) hlen
  simpa [hsub] using cantorLeft_separated_of_length_eq (ds := ds) (ds' := ds') hlen hne

/-- The explicit interval corresponding to a digit list `ds`. -/
noncomputable def cantorCylinderInterval (ds : List Bool) : Set ℝ :=
  Set.Icc (cantorLeft ds) (cantorLeft ds + cantorWidth ds)

theorem cantorCylinderInterval_subset_Icc (ds : List Bool) : cantorCylinderInterval ds ⊆ Set.Icc (0 : ℝ) 1 := by
  intro x hx
  refine ⟨?_, ?_⟩
  · -- `0 ≤ cantorLeft ds ≤ x`.
    exact le_trans (cantorLeft_nonneg ds) hx.1
  · -- `x ≤ cantorLeft ds + width ≤ 1`.
    exact le_trans hx.2 (cantorLeft_add_width_le_one ds)

theorem mem_cantorCylinder_iff_mem_interval : ∀ (ds : List Bool) (x : ℝ),
    x ∈ cantorCylinder ds ↔ x ∈ cantorCylinderInterval ds := by
  intro ds
  induction ds with
  | nil =>
      intro x
      simp [cantorCylinder, cantorCylinderInterval, cantorLeft, cantorWidth]
  | cons b ds ih =>
      intro x
      cases b with
      | false =>
          -- `x ∈ [0,1/3]` and `3x ∈ cylinder ds`.
          constructor
          · intro hx
            have hxH : x ∈ cantorHeadInterval false := hx.1
            have hxT : cantorTailAffine false x ∈ cantorCylinder ds := hx.2
            have hxT' : (3 * x) ∈ cantorCylinderInterval ds := (ih (3 * x)).1 (by simpa [cantorTailAffine] using hxT)
            rcases hxT' with ⟨hL, hU⟩
            -- Divide bounds by 3.
            have hL' : (oneThird : ℝ) * cantorLeft ds ≤ x := by
              have : cantorLeft ds ≤ 3 * x := hL
              -- multiply by 1/3
              nlinarith [this]
            have hU' : x ≤ (oneThird : ℝ) * (cantorLeft ds + cantorWidth ds) := by
              have : 3 * x ≤ cantorLeft ds + cantorWidth ds := hU
              nlinarith [this]
            -- Show membership in the cons-interval.
            have hx0 : 0 ≤ x := (by
              have hxI : x ∈ Set.Icc (0 : ℝ) oneThird := by simpa [cantorHeadInterval] using hxH
              exact hxI.1)
            have hx13 : x ≤ oneThird := (by
              have hxI : x ∈ Set.Icc (0 : ℝ) oneThird := by simpa [cantorHeadInterval] using hxH
              exact hxI.2)
            refine ⟨?_, ?_⟩
            · -- lower bound is `left(false::ds)`.
              simpa [cantorCylinderInterval, cantorLeft, cantorWidth_cons, oneThird, twoThird, hx0] using hL'
            · -- upper bound is `left + width`.
              -- `x ≤ (left+width)/3` and `(left+width) ≤ 1` gives `x ≤ 1/3`, consistent.
              have : x ≤ (oneThird : ℝ) * cantorLeft ds + (oneThird : ℝ) * cantorWidth ds := by
                simpa [mul_add] using hU'
              simpa [cantorCylinderInterval, cantorLeft, cantorWidth_cons, oneThird, mul_add, add_assoc, add_left_comm,
                add_comm] using this
          · intro hx
            -- Unpack interval bounds for `false::ds`.
            have hxL : (oneThird : ℝ) * cantorLeft ds ≤ x := by
              have : cantorLeft (false :: ds) ≤ x := hx.1
              simpa [cantorCylinderInterval, cantorLeft, oneThird, twoThird] using this
            have hxU : x ≤ (oneThird : ℝ) * (cantorLeft ds + cantorWidth ds) := by
              have : x ≤ cantorLeft (false :: ds) + cantorWidth (false :: ds) := hx.2
              simpa [cantorCylinderInterval, cantorLeft, cantorWidth_cons, oneThird, twoThird, mul_add, add_assoc,
                add_left_comm, add_comm] using this
            -- Show head interval membership.
            have hx0 : 0 ≤ x := le_trans (by
              have : 0 ≤ cantorLeft ds := cantorLeft_nonneg ds
              nlinarith [this]) hxL
            have hx13 : x ≤ oneThird := by
              have hsum : cantorLeft ds + cantorWidth ds ≤ (1 : ℝ) := cantorLeft_add_width_le_one ds
              have : (oneThird : ℝ) * (cantorLeft ds + cantorWidth ds) ≤ oneThird := by
                nlinarith [hsum]
              exact le_trans hxU this
            have hxH : x ∈ cantorHeadInterval false := by
              simpa [cantorHeadInterval] using And.intro hx0 hx13
            -- Tail membership via IH.
            have hxT : 3 * x ∈ cantorCylinderInterval ds := by
              refine And.intro ?_ ?_
              · nlinarith [hxL]
              · nlinarith [hxU]
            have hxC : 3 * x ∈ cantorCylinder ds := (ih (3 * x)).2 hxT
            exact ⟨hxH, by simpa [cantorTailAffine] using hxC⟩
      | true =>
          constructor
          · intro hx
            have hxH : x ∈ cantorHeadInterval true := hx.1
            have hxT : cantorTailAffine true x ∈ cantorCylinder ds := hx.2
            have hxT' : (3 * x - 2) ∈ cantorCylinderInterval ds :=
              (ih (3 * x - 2)).1 (by simpa [cantorTailAffine] using hxT)
            rcases hxT' with ⟨hL, hU⟩
            -- Convert bounds on `3x-2` to bounds on `x`.
            have hL' : (twoThird : ℝ) + (oneThird : ℝ) * cantorLeft ds ≤ x := by
              have : cantorLeft ds ≤ 3 * x - 2 := hL
              nlinarith [this]
            have hU' : x ≤ (twoThird : ℝ) + (oneThird : ℝ) * (cantorLeft ds + cantorWidth ds) := by
              have : 3 * x - 2 ≤ cantorLeft ds + cantorWidth ds := hU
              nlinarith [this]
            refine ⟨?_, ?_⟩
            · simpa [cantorCylinderInterval, cantorLeft, cantorWidth_cons, oneThird, twoThird, mul_add, add_assoc,
                add_left_comm, add_comm] using hL'
            · have : x ≤ (twoThird : ℝ) + (oneThird : ℝ) * cantorLeft ds + (oneThird : ℝ) * cantorWidth ds := by
                simpa [mul_add, add_assoc] using hU'
              simpa [cantorCylinderInterval, cantorLeft, cantorWidth_cons, oneThird, twoThird, mul_add, add_assoc,
                add_left_comm, add_comm] using this
          · intro hx
            have hxL :
                (twoThird : ℝ) + (oneThird : ℝ) * cantorLeft ds ≤ x := by
              have : cantorLeft (true :: ds) ≤ x := hx.1
              simpa [cantorCylinderInterval, cantorLeft, oneThird, twoThird] using this
            have hxU :
                x ≤ (twoThird : ℝ) + (oneThird : ℝ) * (cantorLeft ds + cantorWidth ds) := by
              have : x ≤ cantorLeft (true :: ds) + cantorWidth (true :: ds) := hx.2
              simpa [cantorCylinderInterval, cantorLeft, cantorWidth_cons, oneThird, twoThird, mul_add, add_assoc,
                add_left_comm, add_comm] using this
            -- Head interval membership.
            have hx23 : twoThird ≤ x := by
              have : 0 ≤ (oneThird : ℝ) * cantorLeft ds := by
                have : 0 ≤ cantorLeft ds := cantorLeft_nonneg ds
                nlinarith [this]
              nlinarith [hxL, this]
            have hx1 : x ≤ (1 : ℝ) := by
              have hsum : cantorLeft ds + cantorWidth ds ≤ (1 : ℝ) := cantorLeft_add_width_le_one ds
              have : (twoThird : ℝ) + (oneThird : ℝ) * (cantorLeft ds + cantorWidth ds) ≤ 1 := by
                -- `2/3 + (left+width)/3 ≤ 1`.
                nlinarith [hsum, oneThird, twoThird]
              exact le_trans hxU this
            have hxH : x ∈ cantorHeadInterval true := by
              simpa [cantorHeadInterval] using And.intro hx23 hx1
            -- Tail membership via IH.
            have hxT : (3 * x - 2) ∈ cantorCylinderInterval ds := by
              refine And.intro ?_ ?_
              · nlinarith [hxL]
              · nlinarith [hxU]
            have hxC : (3 * x - 2) ∈ cantorCylinder ds := (ih (3 * x - 2)).2 hxT
            exact ⟨hxH, by simpa [cantorTailAffine] using hxC⟩

theorem cantorCylinder_eq_interval (ds : List Bool) :
    cantorCylinder ds = cantorCylinderInterval ds := by
  ext x
  simpa using (mem_cantorCylinder_iff_mem_interval ds x)

theorem cantorCylinderInterval_disjoint_of_length_eq {ds ds' : List Bool} (hlen : ds.length = ds'.length)
    (hne : ds ≠ ds') :
    Disjoint (cantorCylinderInterval ds) (cantorCylinderInterval ds') := by
  -- Reduce to disjointness of the corresponding cylinder *sets* (`CantorCylinders.lean`).
  have hd : Disjoint (cantorCylinder ds) (cantorCylinder ds') :=
    cantorCylinder_disjoint_of_length_eq (ds := ds) (ds' := ds') hlen hne
  -- Rewrite cylinders as explicit intervals.
  simpa [cantorCylinder_eq_interval] using hd

end Billiards
end MirandaDynamics
end HeytingLean
