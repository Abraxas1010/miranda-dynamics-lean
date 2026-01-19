import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteNoSpurious
import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteWallsAppendix

/-!
# MirandaDynamics.Billiards: Appendix-consistent rewrite redirecting walls `\\widetilde W^{rw}` (WS7.3)

The Appendix “symbol change” (rewrite) gadget perturbs the slope of the separating wall segments
(`rwWallRewrite`) and produces a slightly different horizontal displacement on the way down to the
redirecting walls.

This file introduces a second, Appendix-consistent family of **redirecting** walls for the rewrite
case:

* `shiftRewrite k ds cur` adjusts the `±2` horizontal shift by `± 2 * rwBlockLen k ds`;
* `tildeWallRewriteAppendix k ds cur` is the translate of `rwWallRewrite k ds cur` by
  `(shiftRewrite k ds cur, -2)`.

These definitions are *geometry data* only; the corridor-level deterministic “next collision” and
avoidance proofs live in dedicated `...Deterministic` files.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set
open Plane

namespace PaperReadWrite

/-- Appendix-style rewrite horizontal shift: `shift cur` corrected by `± 2 * rwBlockLen`. -/
noncomputable def shiftRewrite (k : ℤ) (ds : List Bool) (cur : Bool) : ℝ :=
  shift cur + (if cur then -(2 * rwBlockLen k ds) else (2 * rwBlockLen k ds))

/-! ## Canonical-length invariance (`rwDigits`) -/

private theorem ds_length_eq_of_rwDigits (k : ℤ) {pref : List Bool} {cur : Bool}
    (h : PaperReadWriteBoundary.rwDigits k pref cur) :
    (pref ++ [cur]).length = indexNat k + 1 := by
  simpa [PaperReadWriteBoundary.rwDigits, List.length_append] using congrArg (fun n => n + 1) h

theorem rwBlockLen_eq_of_rwDigits (k : ℤ) {pref pref' : List Bool} {cur cur' : Bool}
    (h : PaperReadWriteBoundary.rwDigits k pref cur) (h' : PaperReadWriteBoundary.rwDigits k pref' cur') :
    rwBlockLen k (pref ++ [cur]) = rwBlockLen k (pref' ++ [cur']) := by
  have hlen :
      (pref ++ [cur]).length = (pref' ++ [cur']).length := by
    simpa [ds_length_eq_of_rwDigits (k := k) (pref := pref) (cur := cur) h,
      ds_length_eq_of_rwDigits (k := k) (pref := pref') (cur := cur') h']
  simpa using (rwBlockLen_eq_of_length_eq (k := k) (ds := pref ++ [cur]) (ds' := pref' ++ [cur']) hlen)

theorem shiftRewrite_eq_of_rwDigits (k : ℤ) {pref pref' : List Bool} {cur : Bool}
    (h : PaperReadWriteBoundary.rwDigits k pref cur) (h' : PaperReadWriteBoundary.rwDigits k pref' cur) :
    shiftRewrite k (pref ++ [cur]) cur = shiftRewrite k (pref' ++ [cur]) cur := by
  have hlen :
      (pref ++ [cur]).length = (pref' ++ [cur]).length := by
    simp [ds_length_eq_of_rwDigits (k := k) (pref := pref) (cur := cur) h,
      ds_length_eq_of_rwDigits (k := k) (pref := pref') (cur := cur) h']
  exact shiftRewrite_eq_of_length_eq (k := k) (cur := cur) (ds := pref ++ [cur]) (ds' := pref' ++ [cur]) hlen

theorem rewriteSlope_eq_of_rwDigits (k : ℤ) {pref pref' : List Bool} {cur : Bool}
    (h : PaperReadWriteBoundary.rwDigits k pref cur) (h' : PaperReadWriteBoundary.rwDigits k pref' cur) :
    rewriteSlope k (pref ++ [cur]) = rewriteSlope k (pref' ++ [cur]) := by
  have hlen :
      rwBlockLen k (pref ++ [cur]) = rwBlockLen k (pref' ++ [cur]) :=
    rwBlockLen_eq_of_rwDigits (k := k) (pref := pref) (pref' := pref') (cur := cur) (cur' := cur) h h'
  simp [rewriteSlope, hlen]

/-! ## Quantitative bounds for canonical lengths (useful for cross-`k` gap arguments) -/

private theorem cantorWidth_le_inv_pow_of_le_length {ds : List Bool} {n : ℕ} (hn : n ≤ ds.length) :
    cantorWidth ds ≤ ((3 : ℝ) ^ n)⁻¹ := by
  -- `cantorWidth ds = (3^len)⁻¹` and `n ≤ len` implies `3^n ≤ 3^len`, hence invert.
  have hpow : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ ds.length :=
    pow_le_pow_right₀ (by norm_num) hn
  have hpos : 0 < (3 : ℝ) ^ n := by positivity
  have hinv : ((3 : ℝ) ^ ds.length)⁻¹ ≤ ((3 : ℝ) ^ n)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hpos hpow
  simpa [cantorWidth] using hinv

private theorem cantorWidth_le_one_ninth_of_length_ge_two (ds : List Bool) (hn : 2 ≤ ds.length) :
    cantorWidth ds ≤ (1 / 9 : ℝ) := by
  have := cantorWidth_le_inv_pow_of_le_length (ds := ds) (n := 2) hn
  simpa using this

private theorem cantorWidth_le_one_twentyseven_of_length_ge_three (ds : List Bool) (hn : 3 ≤ ds.length) :
    cantorWidth ds ≤ (1 / 27 : ℝ) := by
  have := cantorWidth_le_inv_pow_of_le_length (ds := ds) (n := 3) hn
  simpa using this

theorem rwBlockLen_le_headScale_div_ninth_of_rwDigits_neg (k : ℤ) (hk : k < 0) {pref : List Bool} {cur : Bool}
    (h : PaperReadWriteBoundary.rwDigits k pref cur) :
    rwBlockLen k (pref ++ [cur]) ≤ headScale k / 9 := by
  -- For `k < 0`, `indexNat k = 2*n+1`, so `length(pref++[cur]) = indexNat k + 1 ≥ 2`.
  have hlen_ge : (2 : ℕ) ≤ (pref ++ [cur]).length := by
    have hlen : (pref ++ [cur]).length = indexNat k + 1 := ds_length_eq_of_rwDigits (k := k) (pref := pref) (cur := cur) h
    -- `k < 0` means `k = Int.negSucc n`, hence `indexNat k = 2*n+1 ≥ 1`, so `+1 ≥ 2`.
    cases k with
    | ofNat n =>
      exfalso
      have : ¬((Int.ofNat n : ℤ) < 0) := not_lt_of_ge (Int.natCast_nonneg n)
      exact this hk
    | negSucc n =>
      -- `indexNat (negSucc n) = 2*n+1`.
      have : (2 : ℕ) ≤ indexNat (Int.negSucc n) + 1 := by
        -- `indexNat = 2*n+1`, so `+1 = 2*n+2 ≥ 2`.
        simpa [indexNat] using (Nat.le_add_left 2 (2 * n))
      simpa [hlen] using this
  have hw : cantorWidth (pref ++ [cur]) ≤ (1 / 9 : ℝ) :=
    cantorWidth_le_one_ninth_of_length_ge_two (pref ++ [cur]) hlen_ge
  have hs0 : 0 ≤ headScale k := le_of_lt (headScale_pos k)
  -- `rwBlockLen = headScale * cantorWidth ≤ headScale * (1/9)`.
  have : rwBlockLen k (pref ++ [cur]) ≤ headScale k * (1 / 9 : ℝ) := by
    simpa [rwBlockLen] using (mul_le_mul_of_nonneg_left hw hs0)
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this

theorem rwBlockLen_le_headScale_div_twentyseven_of_rwDigits_pos (k : ℤ) (hk : 0 < k) {pref : List Bool} {cur : Bool}
    (h : PaperReadWriteBoundary.rwDigits k pref cur) :
    rwBlockLen k (pref ++ [cur]) ≤ headScale k / 27 := by
  -- For `k > 0`, `k = Int.ofNat (n+1)` so `indexNat k = 2*(n+1) ≥ 2`, hence `length ≥ 3`.
  have hlen_ge : (3 : ℕ) ≤ (pref ++ [cur]).length := by
    have hlen : (pref ++ [cur]).length = indexNat k + 1 := ds_length_eq_of_rwDigits (k := k) (pref := pref) (cur := cur) h
    cases k with
    | negSucc n =>
      exfalso
      have : (Int.negSucc n : ℤ) < 0 := Int.negSucc_lt_zero n
      exact (not_lt_of_gt this) hk
    | ofNat n =>
      -- `0 < ofNat n` implies `n ≥ 1`.
      have hn : 1 ≤ n := by
        -- `0 < (n:ℤ)` ↔ `0 < n` for naturals.
        exact Nat.succ_le_iff.2 (Int.ofNat_lt.1 hk)
      have : (3 : ℕ) ≤ indexNat (Int.ofNat n) + 1 := by
        -- `indexNat (ofNat n) = 2*n`, so `2*n+1 ≥ 3` when `n ≥ 1`.
        have : 3 ≤ 2 * n + 1 := by nlinarith
        simpa [indexNat, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
      simpa [hlen] using this
  have hw : cantorWidth (pref ++ [cur]) ≤ (1 / 27 : ℝ) :=
    cantorWidth_le_one_twentyseven_of_length_ge_three (pref ++ [cur]) hlen_ge
  have hs0 : 0 ≤ headScale k := le_of_lt (headScale_pos k)
  have : rwBlockLen k (pref ++ [cur]) ≤ headScale k * (1 / 27 : ℝ) := by
    simpa [rwBlockLen] using (mul_le_mul_of_nonneg_left hw hs0)
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this

theorem rwBlockLen_eq_headScale_mul_inv_pow_length (k : ℤ) (ds : List Bool) :
    rwBlockLen k ds = headScale k * ((3 : ℝ) ^ ds.length)⁻¹ := by
  simp [rwBlockLen, cantorWidth]

theorem rwBlockLen_eq_headScale_mul_inv_pow_indexNat_succ (k : ℤ) {pref : List Bool} {cur : Bool}
    (h : PaperReadWriteBoundary.rwDigits k pref cur) :
    rwBlockLen k (pref ++ [cur]) = headScale k * ((3 : ℝ) ^ (indexNat k + 1))⁻¹ := by
  have hlen : (pref ++ [cur]).length = indexNat k + 1 := ds_length_eq_of_rwDigits (k := k) (pref := pref) (cur := cur) h
  simpa [rwBlockLen_eq_headScale_mul_inv_pow_length, hlen]

theorem shiftRewrite_eq_of_rwBlockLen_eq (k : ℤ) {ds ds' : List Bool} (cur : Bool)
    (hlen : rwBlockLen k ds = rwBlockLen k ds') :
    shiftRewrite k ds cur = shiftRewrite k ds' cur := by
  simp [shiftRewrite, hlen]

theorem shiftRewrite_eq_of_length_eq (k : ℤ) {ds ds' : List Bool} (cur : Bool)
    (hlen : ds.length = ds'.length) :
    shiftRewrite k ds cur = shiftRewrite k ds' cur := by
  refine shiftRewrite_eq_of_rwBlockLen_eq (k := k) (cur := cur) (ds := ds) (ds' := ds') ?_
  simpa using (rwBlockLen_eq_of_length_eq (k := k) (ds := ds) (ds' := ds') hlen)

/-- Appendix-consistent redirecting wall for the rewrite case: translate `rwWallRewrite` down by `2`
and horizontally by `shiftRewrite`. -/
def tildeWallRewriteAppendix (k : ℤ) (ds : List Bool) (cur : Bool) : Set V :=
  { p |
      x p ∈ Set.Icc (rwBlockLeft k ds + shiftRewrite k ds cur)
        (rwBlockLeft k ds + shiftRewrite k ds cur + rwBlockLen k ds) ∧
      y p =
        (if cur
         then (rewriteSlope k ds) * (-rwBlockCenter k ds + (x p - shiftRewrite k ds cur))
         else (rewriteSlope k ds) * (rwBlockCenter k ds - (x p - shiftRewrite k ds cur))) }

theorem mem_tildeWallRewriteAppendix_iff (k : ℤ) (ds : List Bool) (cur : Bool) (p : V) :
    p ∈ tildeWallRewriteAppendix k ds cur ↔
      x p ∈ Set.Icc (rwBlockLeft k ds + shiftRewrite k ds cur)
        (rwBlockLeft k ds + shiftRewrite k ds cur + rwBlockLen k ds) ∧
      y p =
        (if cur
         then (rewriteSlope k ds) * (-rwBlockCenter k ds + (x p - shiftRewrite k ds cur))
         else (rewriteSlope k ds) * (rwBlockCenter k ds - (x p - shiftRewrite k ds cur))) :=
  Iff.rfl

theorem mem_tildeWallRewriteAppendix_iff_sub_shiftRewrite (k : ℤ) (ds : List Bool) (cur : Bool) (p : V) :
    p ∈ tildeWallRewriteAppendix k ds cur ↔
      (x p - shiftRewrite k ds cur) ∈ rwBlockInterval k ds ∧
        y p =
          (if cur
           then (rewriteSlope k ds) * (-rwBlockCenter k ds + (x p - shiftRewrite k ds cur))
           else (rewriteSlope k ds) * (rwBlockCenter k ds - (x p - shiftRewrite k ds cur))) := by
  constructor <;> intro hp
  · rcases hp with ⟨hx, hy⟩
    refine ⟨?_, hy⟩
    rcases hx with ⟨hxL, hxU⟩
    constructor <;> linarith
  · rcases hp with ⟨hx, hy⟩
    refine ⟨?_, hy⟩
    rcases hx with ⟨hxL, hxU⟩
    constructor <;> linarith

/-- Canonical union of Appendix rewrite redirecting walls `tildeWallRewriteAppendix k (pref++[cur]) cur`. -/
def tildeWallRewriteAppendixUnionCanonical : Set V :=
  { p |
      ∃ k : ℤ, ∃ pref : List Bool, ∃ cur : Bool,
        PaperReadWriteBoundary.rwDigits k pref cur ∧ p ∈ tildeWallRewriteAppendix k (pref ++ [cur]) cur }

/-- `tildeWallRewriteAppendix` is a translation of `rwWallRewrite` by `(shiftRewrite cur, -2)`. -/
theorem tildeWallRewriteAppendix_eq_image_translate_rwWallRewrite (k : ℤ) (ds : List Bool) (cur : Bool) :
    tildeWallRewriteAppendix k ds cur =
      (fun p : V => p + (shiftRewrite k ds cur) • eX + (-2 : ℝ) • eY) '' (rwWallRewrite k ds cur) := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨hx, hy⟩
    let q : V := p + (-shiftRewrite k ds cur) • eX + (2 : ℝ) • eY
    have hxq : x q ∈ rwBlockInterval k ds := by
      rcases hx with ⟨hxL, hxU⟩
      have hxq' : x q = x p - shiftRewrite k ds cur := by
        simp [q, Plane.x, Plane.eX, Plane.eY, add_assoc, add_left_comm, add_comm]
      constructor <;> linarith [hxq']
    have hyq :
        y q =
          (2 : ℝ) +
            (if cur
             then (rewriteSlope k ds) * (-rwBlockCenter k ds + x q)
             else (rewriteSlope k ds) * (rwBlockCenter k ds - x q)) := by
      have hyq' : y q = y p + 2 := by
        simp [q, Plane.y, Plane.eX, Plane.eY, add_assoc, add_left_comm, add_comm]
      have hxq' : x q = x p - shiftRewrite k ds cur := by
        simp [q, Plane.x, Plane.eX, Plane.eY, add_assoc, add_left_comm, add_comm]
      cases cur <;>
        simp [tildeWallRewriteAppendix, hy, hyq', hxq', rwWallRewrite, sub_eq_add_neg] <;>
        ring_nf
    have hq : q ∈ rwWallRewrite k ds cur := by
      refine ⟨hxq, ?_⟩
      simpa [rwWallRewrite, hyq]
    refine ⟨q, hq, ?_⟩
    have : p = q + (shiftRewrite k ds cur) • eX + (-2 : ℝ) • eY := by
      simp [q, add_assoc, add_left_comm, add_comm]
    simpa [this]
  · rintro ⟨q, hq, rfl⟩
    rcases hq with ⟨hxq, hyq⟩
    refine ⟨?_, ?_⟩
    · rcases hxq with ⟨hxL, hxU⟩
      have hx :
          x (q + (shiftRewrite k ds cur) • eX + (-2 : ℝ) • eY) =
            x q + shiftRewrite k ds cur := by
        simp [Plane.x, Plane.eX, Plane.eY, add_assoc, add_left_comm, add_comm]
      constructor <;> linarith [hx]
    · have hy : y (q + (shiftRewrite k ds cur) • eX + (-2 : ℝ) • eY) = y q - 2 := by
        simp [Plane.y, Plane.eX, Plane.eY, add_assoc, add_left_comm, add_comm]
      have hx : x (q + (shiftRewrite k ds cur) • eX + (-2 : ℝ) • eY) - shiftRewrite k ds cur = x q := by
        simp [Plane.x, Plane.eX, Plane.eY, add_assoc, add_left_comm, add_comm]
      cases cur <;>
        simp [tildeWallRewriteAppendix, hy, hx, rwWallRewrite, sub_eq_add_neg] at hyq ⊢ <;>
        linarith

/-! ## Basic disjointness (same `k`, same `cur`) -/

/-- Distinct blocks with the same `k` and `cur` give disjoint rewrite-redirecting walls. -/
theorem tildeWallRewriteAppendix_disjoint_of_length_eq (k : ℤ) {ds ds' : List Bool}
    (hlen : ds.length = ds'.length) (hne : ds ≠ ds') (cur : Bool) :
    Disjoint (tildeWallRewriteAppendix k ds cur) (tildeWallRewriteAppendix k ds' cur) := by
  classical
  refine Set.disjoint_left.2 ?_
  intro p hp hp'
  have hshift : shiftRewrite k ds cur = shiftRewrite k ds' cur :=
    shiftRewrite_eq_of_length_eq (k := k) (cur := cur) (ds := ds) (ds' := ds') hlen
  have hx : (x p - shiftRewrite k ds cur) ∈ rwBlockInterval k ds :=
    (mem_tildeWallRewriteAppendix_iff_sub_shiftRewrite (k := k) (ds := ds) (cur := cur) (p := p)).1 hp |>.1
  have hx' : (x p - shiftRewrite k ds cur) ∈ rwBlockInterval k ds' := by
    have hx0 :
        (x p - shiftRewrite k ds' cur) ∈ rwBlockInterval k ds' :=
      (mem_tildeWallRewriteAppendix_iff_sub_shiftRewrite (k := k) (ds := ds') (cur := cur) (p := p)).1 hp' |>.1
    simpa [hshift] using hx0
  have hdis : Disjoint (rwBlockInterval k ds) (rwBlockInterval k ds') :=
    rwBlockInterval_disjoint_of_length_eq (k := k) (ds := ds) (ds' := ds') hlen hne
  exact (Set.disjoint_left.1 hdis) hx hx'

/-! ## Coarse `x`-strip localization (useful for collision-branch identification) -/

private theorem cantorWidth_le_one (ds : List Bool) : cantorWidth ds ≤ (1 : ℝ) := by
  -- `cantorWidth ds = (3^len)⁻¹ ≤ 1` since `1 ≤ 3^len`.
  have hbase : (1 : ℝ) ≤ (3 : ℝ) := by norm_num
  have hpow : (1 : ℝ) ≤ (3 : ℝ) ^ ds.length := by
    simpa using (one_le_pow_of_one_le hbase ds.length)
  simpa [cantorWidth] using (inv_le_one_of_one_le₀ hpow)

private theorem rwBlockLen_le_one_third (k : ℤ) (ds : List Bool) : rwBlockLen k ds ≤ (1 / 3 : ℝ) := by
  have hs : headScale k ≤ (1 / 3 : ℝ) := headScale_le_one_third k
  have hw : cantorWidth ds ≤ (1 : ℝ) := cantorWidth_le_one ds
  -- `rwBlockLen = headScale * cantorWidth ≤ headScale`.
  have : rwBlockLen k ds ≤ headScale k := by
    dsimp [rwBlockLen]
    have hs0 : 0 ≤ headScale k := le_of_lt (headScale_pos k)
    simpa [mul_one] using (mul_le_mul_of_nonneg_left hw hs0)
  exact le_trans this hs

private theorem rwBlockLeft_le_one (k : ℤ) (ds : List Bool) : rwBlockLeft k ds ≤ (1 : ℝ) := by
  -- `rwBlockLeft` lies in `rwBlockInterval`, hence in `headInterval`, hence in `[0,1]`.
  have hxIcc : rwBlockLeft k ds ∈ rwBlockInterval k ds := by
    have hlen : 0 ≤ rwBlockLen k ds := le_of_lt (rwBlockLen_pos k ds)
    exact ⟨le_rfl, by linarith⟩
  have hxHead : rwBlockLeft k ds ∈ headInterval k :=
    rwBlockInterval_subset_headInterval (k := k) (ds := ds) hxIcc
  exact (headInterval_subset_Icc k hxHead).2

/-- Any rewrite-redirecting wall point lies on the **left strip** `x ≤ 0` when `cur = false`. -/
theorem tildeWallRewriteAppendix_x_le_zero (k : ℤ) (ds : List Bool) {p : V}
    (hp : p ∈ tildeWallRewriteAppendix k ds false) : x p ≤ 0 := by
  rcases (mem_tildeWallRewriteAppendix_iff (k := k) (ds := ds) (cur := false) (p := p)).1 hp with ⟨hx, _hy⟩
  have hxU : x p ≤ rwBlockLeft k ds + shiftRewrite k ds false + rwBlockLen k ds := hx.2
  -- Bound the endpoint by `1 - 4/3 + 1/3 = 0`.
  have hlen : rwBlockLen k ds ≤ (1 / 3 : ℝ) := rwBlockLen_le_one_third k ds
  have hleft : rwBlockLeft k ds ≤ (1 : ℝ) := rwBlockLeft_le_one k ds
  have hshift : shiftRewrite k ds false ≤ (-4 / 3 : ℝ) := by
    -- `shiftRewrite = -2 + 2*len` and `len ≤ 1/3`.
    simp [shiftRewrite, shift, rwBlockLen, add_assoc, add_left_comm, add_comm]
    nlinarith [hlen]
  nlinarith [hxU, hleft, hshift, hlen]

/-- Any rewrite-redirecting wall point lies on the **right strip** `x ≥ 1` when `cur = true`. -/
theorem tildeWallRewriteAppendix_one_le_x (k : ℤ) (ds : List Bool) {p : V}
    (hp : p ∈ tildeWallRewriteAppendix k ds true) : (1 : ℝ) ≤ x p := by
  rcases (mem_tildeWallRewriteAppendix_iff (k := k) (ds := ds) (cur := true) (p := p)).1 hp with ⟨hx, _hy⟩
  have hxL : rwBlockLeft k ds + shiftRewrite k ds true ≤ x p := hx.1
  have hlen : rwBlockLen k ds ≤ (1 / 3 : ℝ) := rwBlockLen_le_one_third k ds
  have hleft0 : (0 : ℝ) ≤ rwBlockLeft k ds := by
    -- Same argument as `rwBlockLeft_le_one`, but take the left inequality.
    have hxIcc : rwBlockLeft k ds ∈ rwBlockInterval k ds := by
      have hlen0 : 0 ≤ rwBlockLen k ds := le_of_lt (rwBlockLen_pos k ds)
      exact ⟨le_rfl, by linarith⟩
    have hxHead : rwBlockLeft k ds ∈ headInterval k :=
      rwBlockInterval_subset_headInterval (k := k) (ds := ds) hxIcc
    exact (headInterval_subset_Icc k hxHead).1
  have hshift : (4 / 3 : ℝ) ≤ shiftRewrite k ds true := by
    -- `shiftRewrite = 2 - 2*len` and `len ≤ 1/3`.
    simp [shiftRewrite, shift, rwBlockLen, add_assoc, add_left_comm, add_comm]
    nlinarith [hlen]
  have : (4 / 3 : ℝ) ≤ rwBlockLeft k ds + shiftRewrite k ds true := by nlinarith [hleft0, hshift]
  exact le_trans (by nlinarith) (le_trans this hxL)

end PaperReadWrite

end Billiards
end MirandaDynamics
end HeytingLean
