import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteFlightAvoidance

/-!
# MirandaDynamics.Billiards: cross-`k` straight-wall flight avoidance lemmas (WS7.3)

`PaperReadWriteFlightAvoidance.lean` packages Appendix-style avoidance lemmas for *same* head index
`k`. The remaining geometric gap requires the same style of argument across *different* head
intervals `I_k` and `I_{k'}`.

This file starts that extension:

* generalize the endpoint separation inequality to `endpointSepCross`;
* prove “intersection forces endpoint” lemmas for `k ≠ k'` under `endpointSepCross`.

It intentionally does **not** claim that `endpointSepCross` always holds: establishing the
quantitative bounds from head-interval separation is a separate (longer) step.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set
open Plane

namespace PaperReadWrite

open PaperReadWriteNoSpurious

/-! ## Cross-`k` endpoint separation wrapper -/

abbrev endpointSepCross (k : ℤ) (ds : List Bool) (k' : ℤ) (ds' : List Bool) : Prop :=
  PaperReadWrite.endpointSepCross k ds k' ds'

/-! ## Quantitative `endpointSepCross` for nonnegative head indices

This is the paper’s “`k ≠ k'`” case specialized to `k,k' ≥ 0`: the gap between head intervals is on
the order of `3^{-(k'+2)}`, while all wall segment half-lengths are on the order of
`3^{-(3k'+2)}` or smaller.

We only use coarse bounds (`cantorWidth ≤ 1/3`) since they already give ample slack.
-/

private theorem cantorWidth_le_one_third_of_length_pos (ds : List Bool) (hlen : 0 < ds.length) :
    cantorWidth ds ≤ (1 / 3 : ℝ) := by
  -- `cantorWidth ds = (3^len)⁻¹ ≤ (3^1)⁻¹ = 1/3` when `1 ≤ len`.
  have hpow : (3 : ℝ) ^ (1 : ℕ) ≤ (3 : ℝ) ^ ds.length := by
    exact pow_le_pow_right₀ (by norm_num) (Nat.succ_le_iff.2 hlen)
  have hpos : 0 < (3 : ℝ) ^ (1 : ℕ) := by positivity
  have hinv : ((3 : ℝ) ^ ds.length)⁻¹ ≤ ((3 : ℝ) ^ (1 : ℕ))⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hpos hpow
  simpa [cantorWidth] using hinv

private theorem negSucc_lt_negSucc_iff (m n : ℕ) :
    (Int.negSucc m : ℤ) < Int.negSucc n ↔ n < m := by
  -- Rewrite both sides as negated `ofNat` terms.
  have hm : (Int.negSucc m : ℤ) = -((m + 1 : ℕ) : ℤ) := by simp [Int.negSucc_eq]
  have hn : (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) := by simp [Int.negSucc_eq]
  constructor
  · intro h
    have h' : -((m + 1 : ℕ) : ℤ) < -((n + 1 : ℕ) : ℤ) := by simpa [hm, hn] using h
    have : ((n + 1 : ℕ) : ℤ) < ((m + 1 : ℕ) : ℤ) := (Int.neg_lt_neg_iff).1 h'
    have : n + 1 < m + 1 := (Int.ofNat_lt).1 this
    exact Nat.lt_of_add_lt_add_right this
  · intro hnm
    have : ((n + 1 : ℕ) : ℤ) < ((m + 1 : ℕ) : ℤ) := (Int.ofNat_lt).2 (Nat.succ_lt_succ hnm)
    have : -((m + 1 : ℕ) : ℤ) < -((n + 1 : ℕ) : ℤ) := (Int.neg_lt_neg_iff).2 this
    simpa [hm, hn] using this

private theorem headScale_ofNat_le_div_three_of_lt (m n : ℕ) (h : m < n) :
    headScale (Int.ofNat n) ≤ headScale (Int.ofNat m) / 3 := by
  -- Compare exponents: `m+2 ≤ 1+n` when `m < n`.
  have hexp : m + 2 ≤ 1 + n := by
    have : m + 1 ≤ n := Nat.succ_le_iff.2 h
    exact Nat.succ_le_succ this
  have hpow : (3 : ℝ) ^ (m + 2) ≤ (3 : ℝ) ^ (1 + n) := by
    exact pow_le_pow_right₀ (by norm_num) hexp
  have hpos : 0 < (3 : ℝ) ^ (m + 2) := by positivity
  have hinv : ((3 : ℝ) ^ (1 + n))⁻¹ ≤ ((3 : ℝ) ^ (m + 2))⁻¹ := by
    -- invert inequality since powers are positive
    simpa [one_div] using one_div_le_one_div_of_le hpos hpow
  -- Rewrite the RHS as `headScale m / 3`.
  have : ((3 : ℝ) ^ (m + 2))⁻¹ = headScale (Int.ofNat m) / 3 := by
    -- `3^(m+2) = 3^(m+1) * 3`.
    simp [headScale, pow_succ, pow_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm]
  simpa [headScale, this] using hinv

private theorem headLeft_sub_headRight_ofNat_ge (m n : ℕ) (h : m < n) :
    headLeft (Int.ofNat n) - headRight (Int.ofNat m) ≥ headScale (Int.ofNat m) / 3 := by
  have hm0 : ¬((m : ℤ) < 0) := not_lt_of_ge (Int.natCast_nonneg m)
  have hn0 : ¬((n : ℤ) < 0) := not_lt_of_ge (Int.natCast_nonneg n)
  -- `headLeft n - headRight m = headScale m - 2*headScale n`.
  have hform :
      headLeft (Int.ofNat n) - headRight (Int.ofNat m) =
        headScale (Int.ofNat m) - 2 * headScale (Int.ofNat n) := by
    simp [headLeft, headRight, hm0, hn0]
    ring_nf
  have hscale : headScale (Int.ofNat n) ≤ headScale (Int.ofNat m) / 3 :=
    headScale_ofNat_le_div_three_of_lt (m := m) (n := n) h
  -- Conclude by linear arithmetic.
  nlinarith [hform, hscale]

private theorem rwBlockLeft_mem_headInterval (k : ℤ) (ds : List Bool) :
    rwBlockLeft k ds ∈ headInterval k := by
  have hx01 : cantorLeft ds ∈ Set.Icc (0 : ℝ) 1 := ⟨cantorLeft_nonneg ds, cantorLeft_le_one ds⟩
  simpa [rwBlockLeft] using (tau_mem_headInterval (k := k) (x := cantorLeft ds) hx01)

private theorem rwBlockRight_mem_headInterval (k : ℤ) (ds : List Bool) :
    (rwBlockLeft k ds + rwBlockLen k ds) ∈ headInterval k := by
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

theorem endpointSepCross_ofNat_of_lt (m n : ℕ) (h : m < n) (ds ds' : List Bool)
    (hds : 0 < ds.length) (hds' : 0 < ds'.length) :
    endpointSepCross (Int.ofNat n) ds (Int.ofNat m) ds' := by
  -- Reduce the LHS to a head-interval gap.
  have hL : headLeft (Int.ofNat n) ≤ rwBlockLeft (Int.ofNat n) ds :=
    (rwBlockLeft_mem_headInterval (k := (Int.ofNat n)) (ds := ds)).1
  have hR : rwBlockLeft (Int.ofNat m) ds' + rwBlockLen (Int.ofNat m) ds' ≤ headRight (Int.ofNat m) :=
    (rwBlockRight_mem_headInterval (k := (Int.ofNat m)) (ds := ds')).2
  have hgap :
      rwBlockLeft (Int.ofNat n) ds - (rwBlockLeft (Int.ofNat m) ds' + rwBlockLen (Int.ofNat m) ds') ≥
        headLeft (Int.ofNat n) - headRight (Int.ofNat m) := by
    nlinarith [hL, hR]
  -- Bound the RHS (sum of half-lengths) by a multiple of `headScale m`.
  have hw' : cantorWidth ds' ≤ (1 / 3 : ℝ) :=
    cantorWidth_le_one_third_of_length_pos ds' hds'
  have hw : cantorWidth ds ≤ (1 / 3 : ℝ) :=
    cantorWidth_le_one_third_of_length_pos ds hds
  have hlenBound' : rwBlockLen (Int.ofNat m) ds' ≤ headScale (Int.ofNat m) / 3 := by
    -- `rwBlockLen = headScale * cantorWidth`.
    have hs : 0 ≤ headScale (Int.ofNat m) := le_of_lt (headScale_pos (Int.ofNat m))
    have := mul_le_mul_of_nonneg_left hw' hs
    simpa [rwBlockLen, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  have hlenBound : rwBlockLen (Int.ofNat n) ds ≤ headScale (Int.ofNat m) / 9 := by
    have hs0 : 0 ≤ headScale (Int.ofNat n) := le_of_lt (headScale_pos (Int.ofNat n))
    have := mul_le_mul_of_nonneg_left hw hs0
    have h1 : rwBlockLen (Int.ofNat n) ds ≤ headScale (Int.ofNat n) / 3 := by
      simpa [rwBlockLen, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    have hscale : headScale (Int.ofNat n) ≤ headScale (Int.ofNat m) / 3 :=
      headScale_ofNat_le_div_three_of_lt (m := m) (n := n) h
    -- Combine: `len ≤ (scale_n)/3 ≤ (scale_m/3)/3 = scale_m/9`.
    nlinarith [h1, hscale]
  have hrhsBound :
      (rwBlockLen (Int.ofNat n) ds) / 2 + (rwBlockLen (Int.ofNat m) ds') / 2 ≤
        (headScale (Int.ofNat m)) / 3 := by
    nlinarith [hlenBound, hlenBound']
  have hheadGap : headLeft (Int.ofNat n) - headRight (Int.ofNat m) ≥ headScale (Int.ofNat m) / 3 :=
    headLeft_sub_headRight_ofNat_ge (m := m) (n := n) h
  -- Conclude.
  dsimp [endpointSepCross, PaperReadWrite.endpointSepCross]
  nlinarith [hgap, hheadGap, hrhsBound]

/-!
## Quantitative `endpointSepCross` for negative head indices

By the reflection symmetry `I_k ↔ 1 - I_{-k}` (`headInterval_reflect` / `headLeft_neg` /
`headRight_neg`), the gap estimate for `k,k' < 0` reduces to the already-proved nonnegative case.

Concretely: for `m < n`, the interval `I_{-(m+1)}` lies strictly to the right of `I_{-(n+1)}`, and
the same coarse bounds (`cantorWidth ≤ 1/3`) give enough slack for `endpointSepCross`.
-/

private theorem headScale_negSucc_le_div_three_of_lt (m n : ℕ) (h : m < n) :
    headScale (Int.negSucc n) ≤ headScale (Int.negSucc m) / 3 := by
  -- Reduce to the `ofNat` statement using `-(negSucc n) = ofNat (n+1)` and `headScale (-k) = headScale k`.
  have h' : m + 1 < n + 1 := Nat.succ_lt_succ h
  have hscale :
      headScale (Int.ofNat (n + 1)) ≤ headScale (Int.ofNat (m + 1)) / 3 :=
    headScale_ofNat_le_div_three_of_lt (m := m + 1) (n := n + 1) h'
  simpa using hscale

private theorem headLeft_sub_headRight_negSucc_ge (m n : ℕ) (h : m < n) :
    headLeft (Int.negSucc m) - headRight (Int.negSucc n) ≥ headScale (Int.negSucc m) / 3 := by
  -- Rewrite the negative-gap as a positive-gap using reflection symmetry about `1/2`.
  have hL : headLeft (Int.negSucc m) = 1 - headRight (-(Int.negSucc m)) := by
    simpa using (headLeft_neg (k := -(Int.negSucc m)))
  have hR : headRight (Int.negSucc n) = 1 - headLeft (-(Int.negSucc n)) := by
    simpa using (headRight_neg (k := -(Int.negSucc n)))
  have hrew :
      headLeft (Int.negSucc m) - headRight (Int.negSucc n) =
        headLeft (-(Int.negSucc n)) - headRight (-(Int.negSucc m)) := by
    nlinarith [hL, hR]
  have hpos : m + 1 < n + 1 := Nat.succ_lt_succ h
  have hposGap :
      headLeft (Int.ofNat (n + 1)) - headRight (Int.ofNat (m + 1)) ≥ headScale (Int.ofNat (m + 1)) / 3 :=
    headLeft_sub_headRight_ofNat_ge (m := m + 1) (n := n + 1) hpos
  -- Normalize the reflected indices and scales.
  have hscaleEq : headScale (Int.ofNat (m + 1)) = headScale (Int.negSucc m) := by
    -- `-(negSucc m) = ofNat (m+1)` and `headScale (-k) = headScale k`.
    simpa using (headScale_neg (Int.negSucc m)).symm
  -- Put everything together.
  have : headLeft (Int.negSucc m) - headRight (Int.negSucc n) ≥ headScale (Int.negSucc m) / 3 := by
    -- Rewrite by `hrew`, simplify the negative indices, then use the positive estimate.
    -- `simp` converts `-(Int.negSucc n)` to `Int.ofNat (n+1)`.
    simpa [hrew, hscaleEq] using hposGap
  exact this

theorem endpointSepCross_negSucc_of_lt (m n : ℕ) (h : m < n) (ds ds' : List Bool)
    (hds : 0 < ds.length) (hds' : 0 < ds'.length) :
    endpointSepCross (Int.negSucc m) ds (Int.negSucc n) ds' := by
  -- Reduce the LHS to a head-interval gap.
  have hL : headLeft (Int.negSucc m) ≤ rwBlockLeft (Int.negSucc m) ds :=
    (rwBlockLeft_mem_headInterval (k := (Int.negSucc m)) (ds := ds)).1
  have hR :
      rwBlockLeft (Int.negSucc n) ds' + rwBlockLen (Int.negSucc n) ds' ≤ headRight (Int.negSucc n) :=
    (rwBlockRight_mem_headInterval (k := (Int.negSucc n)) (ds := ds')).2
  have hgap :
      rwBlockLeft (Int.negSucc m) ds - (rwBlockLeft (Int.negSucc n) ds' + rwBlockLen (Int.negSucc n) ds') ≥
        headLeft (Int.negSucc m) - headRight (Int.negSucc n) := by
    nlinarith [hL, hR]
  -- Bound the RHS (sum of half-lengths) by a multiple of `headScale (-(m+1))`.
  have hw' : cantorWidth ds' ≤ (1 / 3 : ℝ) :=
    cantorWidth_le_one_third_of_length_pos ds' hds'
  have hw : cantorWidth ds ≤ (1 / 3 : ℝ) :=
    cantorWidth_le_one_third_of_length_pos ds hds
  have hlenBound_right : rwBlockLen (Int.negSucc m) ds ≤ headScale (Int.negSucc m) / 3 := by
    have hs : 0 ≤ headScale (Int.negSucc m) := le_of_lt (headScale_pos (Int.negSucc m))
    have := mul_le_mul_of_nonneg_left hw hs
    simpa [rwBlockLen, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  have hlenBound_left : rwBlockLen (Int.negSucc n) ds' ≤ headScale (Int.negSucc m) / 9 := by
    have hs0 : 0 ≤ headScale (Int.negSucc n) := le_of_lt (headScale_pos (Int.negSucc n))
    have := mul_le_mul_of_nonneg_left hw' hs0
    have h1 : rwBlockLen (Int.negSucc n) ds' ≤ headScale (Int.negSucc n) / 3 := by
      simpa [rwBlockLen, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    have hscale : headScale (Int.negSucc n) ≤ headScale (Int.negSucc m) / 3 :=
      headScale_negSucc_le_div_three_of_lt (m := m) (n := n) h
    -- Combine: `len ≤ (scale_n)/3 ≤ (scale_m/3)/3 = scale_m/9`.
    nlinarith [h1, hscale]
  have hrhsBound :
      (rwBlockLen (Int.negSucc m) ds) / 2 + (rwBlockLen (Int.negSucc n) ds') / 2 ≤
        headScale (Int.negSucc m) / 3 := by
    nlinarith [hlenBound_right, hlenBound_left]
  have hheadGap :
      headLeft (Int.negSucc m) - headRight (Int.negSucc n) ≥ headScale (Int.negSucc m) / 3 :=
    headLeft_sub_headRight_negSucc_ge (m := m) (n := n) h
  -- Conclude.
  dsimp [endpointSepCross, PaperReadWrite.endpointSepCross]
  nlinarith [hgap, hheadGap, hrhsBound]

/-!
## Quantitative `endpointSepCross` for mixed-sign indices (`k ≥ 0` and `k' < 0`)

For `k = ofNat n` and `k' = negSucc m`, the head intervals lie on opposite sides of `1/3`:

* `I_{ofNat n} ⊆ [1/3, 1]` (coarse bound),
* `I_{negSucc m} ⊆ [0, 2/9]` (since `|k'| ≥ 1`, hence `headScale k' ≤ 1/9`).

So there is a uniform gap `≥ 1/9`, dwarfing all half-lengths (`≤ headScale/3`).
-/

private theorem headScale_le_one_ninth_of_negSucc (m : ℕ) : headScale (Int.negSucc m) ≤ (1 / 9 : ℝ) := by
  -- `headScale (-(m+1)) = 3^{-(1+(m+1))} = 3^{-(m+2)} ≤ 3^{-2} = 1/9`.
  have hpow : (3 : ℝ) ^ (2 : ℕ) ≤ (3 : ℝ) ^ (1 + Int.natAbs (Int.negSucc m)) := by
    -- `natAbs (negSucc m) = m+1`, so exponent is `m+2 ≥ 2`.
    simpa using (pow_le_pow_right₀ (by norm_num) (by
      simpa [Int.natAbs, Nat.succ_le_succ_iff] using (Nat.le_add_left 1 (m + 1))))
  have hpos : 0 < (3 : ℝ) ^ (2 : ℕ) := by positivity
  have hinv : ((3 : ℝ) ^ (1 + Int.natAbs (Int.negSucc m)))⁻¹ ≤ ((3 : ℝ) ^ (2 : ℕ))⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hpos hpow
  simpa [headScale] using hinv

private theorem headLeft_ofNat_ge_one_third (n : ℕ) : (1 / 3 : ℝ) ≤ headLeft (Int.ofNat n) := by
  -- `headLeft = 1 - 2*headScale`, and `headScale ≤ 1/3`.
  have hn0 : ¬((Int.ofNat n : ℤ) < 0) := not_lt_of_ge (Int.natCast_nonneg n)
  have hs : headScale (Int.ofNat n) ≤ (1 / 3 : ℝ) := headScale_le_one_third (Int.ofNat n)
  have hs2 : 2 * headScale (Int.ofNat n) ≤ (2 / 3 : ℝ) := by nlinarith
  have : 1 - (2 / 3 : ℝ) ≤ 1 - 2 * headScale (Int.ofNat n) := sub_le_sub_left hs2 (1 : ℝ)
  simpa [headLeft, hn0] using this

private theorem headRight_negSucc_le_two_ninth (m : ℕ) : headRight (Int.negSucc m) ≤ (2 / 9 : ℝ) := by
  have hk : (Int.negSucc m : ℤ) < 0 := Int.negSucc_lt_zero m
  have hs : headScale (Int.negSucc m) ≤ (1 / 9 : ℝ) := headScale_le_one_ninth_of_negSucc m
  have : 2 * headScale (Int.negSucc m) ≤ (2 / 9 : ℝ) := by nlinarith
  simpa [headRight, hk] using this

theorem endpointSepCross_ofNat_negSucc (n m : ℕ) (ds ds' : List Bool)
    (hds : 0 < ds.length) (hds' : 0 < ds'.length) :
    endpointSepCross (Int.ofNat n) ds (Int.negSucc m) ds' := by
  -- Reduce the LHS to a uniform head-interval gap.
  have hL : headLeft (Int.ofNat n) ≤ rwBlockLeft (Int.ofNat n) ds :=
    (rwBlockLeft_mem_headInterval (k := (Int.ofNat n)) (ds := ds)).1
  have hR :
      rwBlockLeft (Int.negSucc m) ds' + rwBlockLen (Int.negSucc m) ds' ≤ headRight (Int.negSucc m) :=
    (rwBlockRight_mem_headInterval (k := (Int.negSucc m)) (ds := ds')).2
  have hgap :
      rwBlockLeft (Int.ofNat n) ds - (rwBlockLeft (Int.negSucc m) ds' + rwBlockLen (Int.negSucc m) ds') ≥
        headLeft (Int.ofNat n) - headRight (Int.negSucc m) := by
    nlinarith [hL, hR]
  -- Lower-bound the head gap by `1/9`.
  have hheadGap : headLeft (Int.ofNat n) - headRight (Int.negSucc m) ≥ (1 / 9 : ℝ) := by
    have hL' : (1 / 3 : ℝ) ≤ headLeft (Int.ofNat n) := headLeft_ofNat_ge_one_third n
    have hR' : headRight (Int.negSucc m) ≤ (2 / 9 : ℝ) := headRight_negSucc_le_two_ninth m
    nlinarith [hL', hR']
  -- Upper-bound the RHS (sum of half-lengths) by a tiny number `≤ 1/9`.
  have hw' : cantorWidth ds' ≤ (1 / 3 : ℝ) :=
    cantorWidth_le_one_third_of_length_pos ds' hds'
  have hw : cantorWidth ds ≤ (1 / 3 : ℝ) :=
    cantorWidth_le_one_third_of_length_pos ds hds
  have hlenBound' : rwBlockLen (Int.negSucc m) ds' ≤ headScale (Int.negSucc m) / 3 := by
    have hs0 : 0 ≤ headScale (Int.negSucc m) := le_of_lt (headScale_pos (Int.negSucc m))
    have := mul_le_mul_of_nonneg_left hw' hs0
    simpa [rwBlockLen, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  have hlenBound : rwBlockLen (Int.ofNat n) ds ≤ headScale (Int.ofNat n) / 3 := by
    have hs0 : 0 ≤ headScale (Int.ofNat n) := le_of_lt (headScale_pos (Int.ofNat n))
    have := mul_le_mul_of_nonneg_left hw hs0
    simpa [rwBlockLen, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  have hrhsBound :
      (rwBlockLen (Int.ofNat n) ds) / 2 + (rwBlockLen (Int.negSucc m) ds') / 2 ≤ (1 / 9 : ℝ) := by
    -- Crude: `len ≤ headScale/3 ≤ 1/9` and similarly for the negative side.
    have hsN : headScale (Int.ofNat n) ≤ (1 / 3 : ℝ) := headScale_le_one_third (Int.ofNat n)
    have hsM : headScale (Int.negSucc m) ≤ (1 / 9 : ℝ) := headScale_le_one_ninth_of_negSucc m
    nlinarith [hlenBound, hlenBound', hsN, hsM]
  -- Conclude.
  dsimp [endpointSepCross, PaperReadWrite.endpointSepCross]
  nlinarith [hgap, hheadGap, hrhsBound]

/-! ## Cross-`k` ray disjointness (nonnegative indices) -/

theorem rwWall_false_disjoint_flightRayLeft0_of_ofNat_lt
    (m n : ℕ) (h : m < n) (ds ds' : List Bool)
    (hds : 0 < ds.length) (hds' : 0 < ds'.length) :
    Disjoint
      (rwWall (Int.ofNat m) ds' false ∩ {p : V | x p < rwBlockLeft (Int.ofNat m) ds' + rwBlockLen (Int.ofNat m) ds'})
      (flightRayLeft0 (Int.ofNat n) ds) := by
  have hsep : endpointSepCross (Int.ofNat n) ds (Int.ofNat m) ds' :=
    endpointSepCross_ofNat_of_lt (m := m) (n := n) h ds ds' hds hds'
  have hdis :
      Disjoint
        (rwWall (Int.ofNat m) ds' false ∩ {p : V | x p < rwBlockLeft (Int.ofNat m) ds' + rwBlockLen (Int.ofNat m) ds'})
        (flightLineLeft0 (Int.ofNat n) ds) :=
    rwWall_false_disjoint_flightLineLeft0_of_endpointSepCross
      (k := (Int.ofNat n)) (ds := ds) (k' := (Int.ofNat m)) (ds' := ds') hsep
  exact hdis.mono_right (flightRayLeft0_subset_flightLineLeft0 (k := (Int.ofNat n)) (ds := ds))

theorem rwWall_true_disjoint_flightRayRight1_of_ofNat_lt
    (m n : ℕ) (h : m < n) (ds ds' : List Bool)
    (hds : 0 < ds.length) (hds' : 0 < ds'.length) :
    Disjoint (rwWall (Int.ofNat n) ds' true ∩ {p : V | rwBlockLeft (Int.ofNat n) ds' < x p})
      (flightRayRight1 (Int.ofNat m) ds) := by
  -- This is the symmetric situation: the `k'=n` wall lies to the right of the `k=m` ray.
  have hsep : endpointSepCross (Int.ofNat n) ds' (Int.ofNat m) ds :=
    endpointSepCross_ofNat_of_lt (m := m) (n := n) h ds' ds hds' hds
  have hdis :
      Disjoint (rwWall (Int.ofNat n) ds' true ∩ {p : V | rwBlockLeft (Int.ofNat n) ds' < x p})
        (flightLineRight1 (Int.ofNat m) ds) :=
    rwWall_true_disjoint_flightLineRight1_of_endpointSepCross
      (k := (Int.ofNat m)) (ds := ds) (k' := (Int.ofNat n)) (ds' := ds') hsep
  exact hdis.mono_right (flightRayRight1_subset_flightLineRight1 (k := (Int.ofNat m)) (ds := ds))

/-! ## Cross-`k` ray disjointness (mixed-sign indices) -/

theorem rwWall_false_disjoint_flightRayLeft0_of_negSucc
    (n m : ℕ) (ds ds' : List Bool)
    (hds : 0 < ds.length) (hds' : 0 < ds'.length) :
    Disjoint
      (rwWall (Int.negSucc m) ds' false ∩
        {p : V | x p < rwBlockLeft (Int.negSucc m) ds' + rwBlockLen (Int.negSucc m) ds'})
      (flightRayLeft0 (Int.ofNat n) ds) := by
  have hsep : endpointSepCross (Int.ofNat n) ds (Int.negSucc m) ds' :=
    endpointSepCross_ofNat_negSucc (n := n) (m := m) ds ds' hds hds'
  have hdis :
      Disjoint
        (rwWall (Int.negSucc m) ds' false ∩
          {p : V | x p < rwBlockLeft (Int.negSucc m) ds' + rwBlockLen (Int.negSucc m) ds'})
        (flightLineLeft0 (Int.ofNat n) ds) :=
    rwWall_false_disjoint_flightLineLeft0_of_endpointSepCross
      (k := (Int.ofNat n)) (ds := ds) (k' := (Int.negSucc m)) (ds' := ds') hsep
  exact hdis.mono_right (flightRayLeft0_subset_flightLineLeft0 (k := (Int.ofNat n)) (ds := ds))

theorem rwWall_true_disjoint_flightRayRight1_of_negSucc
    (n m : ℕ) (ds ds' : List Bool)
    (hds : 0 < ds.length) (hds' : 0 < ds'.length) :
    Disjoint
      (rwWall (Int.ofNat n) ds' true ∩ {p : V | rwBlockLeft (Int.ofNat n) ds' < x p})
      (flightRayRight1 (Int.negSucc m) ds) := by
  -- Use `endpointSepCross_ofNat_negSucc` with the roles swapped (ray is on the negative side, wall on the nonnegative).
  have hsep : endpointSepCross (Int.ofNat n) ds' (Int.negSucc m) ds :=
    endpointSepCross_ofNat_negSucc (n := n) (m := m) ds' ds hds' hds
  have hdis :
      Disjoint
        (rwWall (Int.ofNat n) ds' true ∩ {p : V | rwBlockLeft (Int.ofNat n) ds' < x p})
        (flightLineRight1 (Int.negSucc m) ds) :=
    rwWall_true_disjoint_flightLineRight1_of_endpointSepCross
      (k := (Int.negSucc m)) (ds := ds) (k' := (Int.ofNat n)) (ds' := ds') hsep
  exact hdis.mono_right (flightRayRight1_subset_flightLineRight1 (k := (Int.negSucc m)) (ds := ds))

/-! ## Cross-`k` ray disjointness (negative indices) -/

theorem rwWall_false_disjoint_flightRayLeft0_of_negSucc_lt
    (m n : ℕ) (h : m < n) (ds ds' : List Bool)
    (hds : 0 < ds.length) (hds' : 0 < ds'.length) :
    Disjoint
      (rwWall (Int.negSucc n) ds' false ∩
        {p : V | x p < rwBlockLeft (Int.negSucc n) ds' + rwBlockLen (Int.negSucc n) ds'})
      (flightRayLeft0 (Int.negSucc m) ds) := by
  have hsep : endpointSepCross (Int.negSucc m) ds (Int.negSucc n) ds' :=
    endpointSepCross_negSucc_of_lt (m := m) (n := n) h ds ds' hds hds'
  have hdis :
      Disjoint
        (rwWall (Int.negSucc n) ds' false ∩
          {p : V | x p < rwBlockLeft (Int.negSucc n) ds' + rwBlockLen (Int.negSucc n) ds'})
        (flightLineLeft0 (Int.negSucc m) ds) :=
    rwWall_false_disjoint_flightLineLeft0_of_endpointSepCross
      (k := (Int.negSucc m)) (ds := ds) (k' := (Int.negSucc n)) (ds' := ds') hsep
  exact hdis.mono_right (flightRayLeft0_subset_flightLineLeft0 (k := (Int.negSucc m)) (ds := ds))

theorem rwWall_true_disjoint_flightRayRight1_of_negSucc_lt
    (m n : ℕ) (h : m < n) (ds ds' : List Bool)
    (hds : 0 < ds.length) (hds' : 0 < ds'.length) :
    Disjoint
      (rwWall (Int.negSucc m) ds' true ∩ {p : V | rwBlockLeft (Int.negSucc m) ds' < x p})
      (flightRayRight1 (Int.negSucc n) ds) := by
  -- Symmetric: the `k'=-(m+1)` wall lies to the right of the `k=-(n+1)` ray.
  have hsep : endpointSepCross (Int.negSucc m) ds' (Int.negSucc n) ds :=
    endpointSepCross_negSucc_of_lt (m := m) (n := n) h ds' ds hds' hds
  have hdis :
      Disjoint
        (rwWall (Int.negSucc m) ds' true ∩ {p : V | rwBlockLeft (Int.negSucc m) ds' < x p})
        (flightLineRight1 (Int.negSucc n) ds) :=
    rwWall_true_disjoint_flightLineRight1_of_endpointSepCross
      (k := (Int.negSucc n)) (ds := ds) (k' := (Int.negSucc m)) (ds' := ds') hsep
  exact hdis.mono_right (flightRayRight1_subset_flightLineRight1 (k := (Int.negSucc n)) (ds := ds))

/-!
## A unified “`k' < k`” interface (cur=false case)

The Appendix checks collisions with walls `W^{k'}_{…0}` lying **to the left** of the post-bounce
trajectory from `W^k_{…0}`; this is expressed by `k' < k`. The following lemma dispatches to the
sign-specialized estimates above.
-/

theorem rwWall_false_disjoint_flightRayLeft0_of_lt (k k' : ℤ) (hk : k' < k) (ds ds' : List Bool)
    (hds : 0 < ds.length) (hds' : 0 < ds'.length) :
    Disjoint
      (rwWall k' ds' false ∩ {p : V | x p < rwBlockLeft k' ds' + rwBlockLen k' ds'})
      (flightRayLeft0 k ds) := by
  cases k with
  | ofNat n =>
    cases k' with
    | ofNat m =>
      have hmn : m < n := (Int.ofNat_lt).1 hk
      simpa using
        rwWall_false_disjoint_flightRayLeft0_of_ofNat_lt (m := m) (n := n) hmn ds ds' hds hds'
    | negSucc m =>
      simpa using
        rwWall_false_disjoint_flightRayLeft0_of_negSucc (n := n) (m := m) ds ds' hds hds'
  | negSucc n =>
    cases k' with
    | ofNat m =>
      -- Impossible: a nonnegative index cannot lie strictly left of a negative one.
      have hm0 : (0 : ℤ) ≤ Int.ofNat m := Int.ofNat_nonneg m
      have hn0 : (Int.negSucc n : ℤ) < 0 := Int.negSucc_lt_zero n
      exact (not_lt_of_ge hm0 (lt_trans hk hn0)).elim
    | negSucc m =>
      have hnm : n < m := (negSucc_lt_negSucc_iff (m := m) (n := n)).1 hk
      -- `k = -(n+1)` and `k' = -(m+1)` with `k' < k` corresponds to `n < m`;
      -- dispatch to the negative-branch lemma (note the swapped order).
      simpa using
        rwWall_false_disjoint_flightRayLeft0_of_negSucc_lt (m := n) (n := m) hnm ds ds' hds hds'

/-!
## A unified “`k < k'`” interface (cur=true case)

This is the symmetric counterpart of `rwWall_false_disjoint_flightRayLeft0_of_lt`: for `cur=true`
the post-bounce ray travels to the **right**, so the relevant walls satisfy `k < k'`.
-/

theorem rwWall_true_disjoint_flightRayRight1_of_lt (k k' : ℤ) (hk : k < k') (ds ds' : List Bool)
    (hds : 0 < ds.length) (hds' : 0 < ds'.length) :
    Disjoint
      (rwWall k' ds' true ∩ {p : V | rwBlockLeft k' ds' < x p})
      (flightRayRight1 k ds) := by
  cases k with
  | ofNat n =>
    cases k' with
    | ofNat m =>
      have hnm : n < m := (Int.ofNat_lt).1 hk
      -- `rwWall_true_disjoint_flightRayRight1_of_ofNat_lt` is stated with `m<n` and swapped roles.
      simpa using
        rwWall_true_disjoint_flightRayRight1_of_ofNat_lt (m := n) (n := m) hnm ds ds' hds hds'
    | negSucc m =>
      -- Impossible: a nonnegative index cannot be strictly left of a negative one.
      have hn0 : (Int.negSucc m : ℤ) < 0 := Int.negSucc_lt_zero m
      have hn0' : ¬((Int.ofNat n : ℤ) < Int.negSucc m) := by
        have hnonneg : 0 ≤ (Int.ofNat n : ℤ) := Int.ofNat_nonneg n
        exact fun h => not_lt_of_ge hnonneg (lt_trans h hn0)
      exact (hn0' hk).elim
  | negSucc n =>
    cases k' with
    | ofNat m =>
      -- Mixed-sign: always `negSucc n < ofNat m`.
      simpa using
        rwWall_true_disjoint_flightRayRight1_of_negSucc (n := m) (m := n) ds ds' hds hds'
    | negSucc m =>
      have hmn : m < n := (negSucc_lt_negSucc_iff (m := n) (n := m)).1 hk
      simpa using
        rwWall_true_disjoint_flightRayRight1_of_negSucc_lt (m := m) (n := n) hmn ds ds' hds hds'

/-! ## Cross-`k` “line ∩ wall ⇒ endpoint” (cur=false) -/

theorem rwWall_false_mem_flightLineLeft0_imp_rightEndpoint_of_endpointSepCross
    (k : ℤ) (ds : List Bool) (k' : ℤ) (ds' : List Bool)
    (hsep : endpointSepCross k ds k' ds') {p : V}
    (hpWall : p ∈ rwWall k' ds' false) (hpFlight : p ∈ flightLineLeft0 k ds) :
    x p = rwBlockLeft k' ds' + rwBlockLen k' ds' := by
  -- Unpack the wall equation and combine with the flight-line equation.
  have hyWall : y p = (2 : ℝ) + (rwBlockCenter k' ds' - x p) := by
    simpa [rwWall] using hpWall.2
  have hyFlight : y p - x p = (2 : ℝ) + (rwBlockLen k ds) / 2 - rwBlockLeft k ds := hpFlight
  -- Solve for `x p`.
  have hxForm :
      x p =
        (rwBlockLeft k' ds' + (rwBlockLen k' ds') / 2 + rwBlockLeft k ds - (rwBlockLen k ds) / 2) / 2 := by
    have : y p - x p =
        (2 : ℝ) + (rwBlockCenter k' ds' - x p) - x p := by
      linarith [hyWall]
    -- Equate the two expressions for `y-x`.
    have : (2 : ℝ) + (rwBlockCenter k' ds' - x p) - x p =
        (2 : ℝ) + (rwBlockLen k ds) / 2 - rwBlockLeft k ds := by
      linarith [this, hyFlight]
    -- Replace `rwBlockCenter` and rearrange.
    -- `rwBlockCenter = left' + len'/2`.
    have hcenter : rwBlockCenter k' ds' = rwBlockLeft k' ds' + (rwBlockLen k' ds') / 2 := by
      simp [rwBlockCenter]
    -- Now solve.
    nlinarith [this, hcenter]
  -- Use `endpointSepCross` to show `x p ≥ rightEndpoint`.
  have hx_ge : x p ≥ rwBlockLeft k' ds' + rwBlockLen k' ds' := by
    -- From the explicit form, reduce to the numerical inequality in `endpointSepCross`.
    dsimp [endpointSepCross, PaperReadWrite.endpointSepCross] at hsep
    -- `nlinarith` handles the “multiply by 2 and rearrange” arithmetic.
    nlinarith [hxForm, hsep]
  -- But `rwWall` membership bounds `x p ≤ rightEndpoint`.
  have hx_le : x p ≤ rwBlockLeft k' ds' + rwBlockLen k' ds' := hpWall.1.2
  exact le_antisymm hx_le hx_ge

theorem rwWall_false_disjoint_flightLineLeft0_of_endpointSepCross
    (k : ℤ) (ds : List Bool) (k' : ℤ) (ds' : List Bool)
    (hsep : endpointSepCross k ds k' ds') :
    Disjoint (rwWall k' ds' false ∩ {p : V | x p < rwBlockLeft k' ds' + rwBlockLen k' ds'})
      (flightLineLeft0 k ds) := by
  classical
  refine Set.disjoint_left.2 ?_
  intro p hpWall hpFlight
  have hx :
      x p = rwBlockLeft k' ds' + rwBlockLen k' ds' :=
    rwWall_false_mem_flightLineLeft0_imp_rightEndpoint_of_endpointSepCross
      (k := k) (ds := ds) (k' := k') (ds' := ds') hsep hpWall.1 hpFlight
  exact (not_lt_of_ge (by simpa [hx] using le_rfl)) hpWall.2

/-! ## Cross-`k` “line ∩ wall ⇒ endpoint” (cur=true) -/

theorem rwWall_true_mem_flightLineRight1_imp_leftEndpoint_of_endpointSepCross
    (k : ℤ) (ds : List Bool) (k' : ℤ) (ds' : List Bool)
    (hsep : endpointSepCross k' ds' k ds) {p : V}
    (hpWall : p ∈ rwWall k' ds' true) (hpFlight : p ∈ flightLineRight1 k ds) :
    x p = rwBlockLeft k' ds' := by
  -- Unpack the wall equation and combine with the flight-line equation.
  have hyWall : y p = (2 : ℝ) + (-rwBlockCenter k' ds' + x p) := by
    simpa [rwWall] using hpWall.2
  have hyFlight :
      y p + x p =
        (2 : ℝ) + (rwBlockLen k ds) / 2 + (rwBlockLeft k ds + rwBlockLen k ds) := hpFlight
  -- Solve for `x p`.
  have hxForm :
      x p =
        (rwBlockLeft k ds + (rwBlockLen k ds) / 2 + rwBlockLeft k' ds' + (rwBlockLen k' ds') / 2 + rwBlockLen k ds) / 2 := by
    have : y p + x p =
        (2 : ℝ) + (-rwBlockCenter k' ds' + x p) + x p := by
      linarith [hyWall]
    have : (2 : ℝ) + (-rwBlockCenter k' ds' + x p) + x p =
        (2 : ℝ) + (rwBlockLen k ds) / 2 + (rwBlockLeft k ds + rwBlockLen k ds) := by
      linarith [this, hyFlight]
    have hcenter : rwBlockCenter k' ds' = rwBlockLeft k' ds' + (rwBlockLen k' ds') / 2 := by
      simp [rwBlockCenter]
    -- Rearrange into the stated explicit form.
    nlinarith [this, hcenter]
  -- Use `endpointSepCross` to show `x p ≤ leftEndpoint`.
  have hx_le : x p ≤ rwBlockLeft k' ds' := by
    dsimp [endpointSepCross, PaperReadWrite.endpointSepCross] at hsep
    -- `nlinarith` handles the arithmetic once the explicit expression is available.
    nlinarith [hxForm, hsep]
  -- But `rwWall` membership bounds `rwBlockLeft ≤ x p`.
  have hx_ge : rwBlockLeft k' ds' ≤ x p := hpWall.1.1
  exact le_antisymm hx_le hx_ge

theorem rwWall_true_disjoint_flightLineRight1_of_endpointSepCross
    (k : ℤ) (ds : List Bool) (k' : ℤ) (ds' : List Bool)
    (hsep : endpointSepCross k' ds' k ds) :
    Disjoint (rwWall k' ds' true ∩ {p : V | rwBlockLeft k' ds' < x p}) (flightLineRight1 k ds) := by
  classical
  refine Set.disjoint_left.2 ?_
  intro p hpWall hpFlight
  have hx :
      x p = rwBlockLeft k' ds' :=
    rwWall_true_mem_flightLineRight1_imp_leftEndpoint_of_endpointSepCross
      (k := k) (ds := ds) (k' := k') (ds' := ds') hsep hpWall.1 hpFlight
  exact (not_lt_of_ge (by simpa [hx] using le_rfl)) hpWall.2

end PaperReadWrite

end Billiards
end MirandaDynamics
end HeytingLean
