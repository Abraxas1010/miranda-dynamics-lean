import HeytingLean.MirandaDynamics.Billiards.CantorEncoding

/-!
# MirandaDynamics.Billiards: tape write operations on the Cantor encoding (WS7.4)

This file proves that `encodeTape` responds to a single-cell overwrite by adding/removing exactly
one geometric-series term in the underlying `Cardinal.cantorFunction` definition.

This is a mechanizable stepping stone toward the paper’s read/write piecewise-affine maps on Cantor
blocks: the *constant* offset is explicit once the relevant digit is fixed.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Cardinal

/-! ## `tapeIndex`/`indexNat` form a bijection -/

theorem indexNat_tapeIndex (n : ℕ) : indexNat (tapeIndex n) = n := by
  by_cases hn : Even n
  · have hmod : n % 2 = 0 := (Nat.even_iff.1 hn)
    have hmul : 2 * (n / 2) = n := by
      -- `2 * (n / 2) + n % 2 = n` and `n % 2 = 0`.
      simpa [hmod] using (Nat.div_add_mod n 2)
    have hidx : indexNat (tapeIndex n) = 2 * (n / 2) := by
      have ht : tapeIndex n = Int.ofNat (n / 2) := by simp [tapeIndex, hn]
      -- `indexNat` reduces by pattern matching.
      rw [ht]
      rfl
    simpa [hidx] using hmul
  · have hmod : n % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
      · exfalso
        exact hn ((Nat.even_iff.2 h0))
      · exact h1
    have hmul : 2 * (n / 2) + 1 = n := by
      simpa [hmod] using (Nat.div_add_mod n 2)
    have hidx : indexNat (tapeIndex n) = 2 * (n / 2) + 1 := by
      have ht : tapeIndex n = Int.negSucc (n / 2) := by simp [tapeIndex, hn]
      rw [ht]
      rfl
    simpa [hidx] using hmul

theorem tapeIndex_injective : Function.Injective tapeIndex := by
  intro m n hmn
  have := congrArg indexNat hmn
  simpa [indexNat_tapeIndex] using this

/-! ## Writing a single tape cell -/

/-- Overwrite a single tape cell. -/
def Tape.write (t : Tape) (k : ℤ) (b : Bool) : Tape :=
  fun z => if z = k then b else t z

theorem digits_write (t : Tape) (k : ℤ) (b : Bool) :
    digits (Tape.write t k b) = Function.update (digits t) (indexNat k) b := by
  funext n
  classical
  by_cases hn : n = indexNat k
  · subst hn
    simp [digits, Tape.write, Function.update, tapeIndex_indexNat]
  · have htk : tapeIndex n ≠ k := by
      intro hEq
      apply hn
      have := congrArg indexNat hEq
      simpa [indexNat_tapeIndex] using this
    simp [digits, Tape.write, Function.update, hn, htk]

/-! ## Updating `cantorFunction` at one digit -/

private theorem cantorFunction_update_one (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (f : ℕ → Bool) (n : ℕ) (b : Bool) :
    Cardinal.cantorFunction c (Function.update f n b) =
      Cardinal.cantorFunction c f +
        (Cardinal.cantorFunctionAux c (Function.update f n b) n - Cardinal.cantorFunctionAux c f n) := by
  classical
  let g : ℕ → ℝ := Cardinal.cantorFunctionAux c (Function.update f n b)
  let g0 : ℕ → ℝ := Cardinal.cantorFunctionAux c f
  have hg : Summable g := by
    simpa [g] using Cardinal.summable_cantor_function (c := c) (f := Function.update f n b) hc0 hc1
  have hg0 : Summable g0 := by
    simpa [g0] using Cardinal.summable_cantor_function (c := c) (f := f) hc0 hc1
  have htail :
      (∑' m : ℕ, if m = n then (0 : ℝ) else g m) =
        ∑' m : ℕ, if m = n then (0 : ℝ) else g0 m := by
    refine tsum_congr ?_
    intro m
    by_cases hm : m = n
    · simp [hm]
    · simp [g, g0, Cardinal.cantorFunctionAux, Function.update, hm]
  -- Decompose both sums at `n` and compare tails.
  have hgDecomp : (∑' m : ℕ, g m) = g n + ∑' m : ℕ, if m = n then (0 : ℝ) else g m :=
    hg.tsum_eq_add_tsum_ite n
  have hg0Decomp : (∑' m : ℕ, g0 m) = g0 n + ∑' m : ℕ, if m = n then (0 : ℝ) else g0 m :=
    hg0.tsum_eq_add_tsum_ite n
  -- Turn the statement into a tsum identity.
  unfold Cardinal.cantorFunction
  -- Normalize via the decompositions and `abel`.
  calc
    (∑' m : ℕ, g m)
        = g n + ∑' m : ℕ, if m = n then (0 : ℝ) else g m := hgDecomp
    _ = g n + ∑' m : ℕ, if m = n then (0 : ℝ) else g0 m := by simp [htail]
    _ = (g0 n + ∑' m : ℕ, if m = n then (0 : ℝ) else g0 m) + (g n - g0 n) := by
          abel
    _ = (∑' m : ℕ, g0 m) + (g n - g0 n) := by
          simp [hg0Decomp]
    _ = (∑' m : ℕ, g0 m) + (g n - g0 n) := rfl

theorem cantorEncode_updateDigit (f : ℕ → Bool) (n : ℕ) (b : Bool) :
    cantorEncode (Function.update f n b) =
      cantorEncode f +
        (2 / 3 : ℝ) *
          (Cardinal.cantorFunctionAux ((3 : ℝ)⁻¹) (Function.update f n b) n -
            Cardinal.cantorFunctionAux ((3 : ℝ)⁻¹) f n) := by
  have h0 : 0 ≤ ((3 : ℝ)⁻¹) := by positivity
  have h1 : ((3 : ℝ)⁻¹) < 1 := by norm_num
  have hcf :=
    cantorFunction_update_one (c := ((3 : ℝ)⁻¹)) (hc0 := h0) (hc1 := h1) (f := f) (n := n) (b := b)
  unfold cantorEncode
  -- Multiply the `cantorFunction` update law by the scaling factor `(2/3)`.
  calc
    (2 / 3 : ℝ) * Cardinal.cantorFunction (1 / 3 : ℝ) (Function.update f n b)
        = (2 / 3 : ℝ) *
            (Cardinal.cantorFunction (1 / 3 : ℝ) f +
              (Cardinal.cantorFunctionAux ((3 : ℝ)⁻¹) (Function.update f n b) n -
                Cardinal.cantorFunctionAux ((3 : ℝ)⁻¹) f n)) := by
              -- Normalize `1/3` as `3⁻¹` to match `hcf`.
              simp [one_div, hcf]
    _ = (2 / 3 : ℝ) * Cardinal.cantorFunction (1 / 3 : ℝ) f +
          (2 / 3 : ℝ) *
            (Cardinal.cantorFunctionAux ((3 : ℝ)⁻¹) (Function.update f n b) n -
              Cardinal.cantorFunctionAux ((3 : ℝ)⁻¹) f n) := by
              ring_nf
    _ = cantorEncode f +
          (2 / 3 : ℝ) *
            (Cardinal.cantorFunctionAux ((3 : ℝ)⁻¹) (Function.update f n b) n -
              Cardinal.cantorFunctionAux ((3 : ℝ)⁻¹) f n) := by
              simp [cantorEncode, one_div]

theorem encodeTape_write (t : Tape) (k : ℤ) (b : Bool) :
    encodeTape (Tape.write t k b) =
      encodeTape t +
        (2 / 3 : ℝ) *
          (Cardinal.cantorFunctionAux ((3 : ℝ)⁻¹) (Function.update (digits t) (indexNat k) b)
              (indexNat k) -
            Cardinal.cantorFunctionAux ((3 : ℝ)⁻¹) (digits t) (indexNat k)) := by
  -- Reduce to `cantorEncode_updateDigit` using the digit-level overwrite lemma.
  have hdigits : digits (Tape.write t k b) = Function.update (digits t) (indexNat k) b :=
    digits_write t k b
  unfold encodeTape
  simpa [hdigits, one_div] using cantorEncode_updateDigit (f := digits t) (n := indexNat k) (b := b)

/-! ## A more explicit “affine” update law -/

theorem encodeTape_write_eq_add_pow (t : Tape) (k : ℤ) (b : Bool) :
    encodeTape (Tape.write t k b) =
      encodeTape t +
        (2 / 3 : ℝ) *
          ((bif b then ((3 : ℝ)⁻¹) ^ (indexNat k) else 0) -
            (bif t k then ((3 : ℝ)⁻¹) ^ (indexNat k) else 0)) := by
  -- `cantorFunctionAux` is a single-digit geometric term, so the overwrite changes only that term.
  simp [encodeTape_write, Cardinal.cantorFunctionAux, Function.update, digits, tapeIndex_indexNat]

end Billiards
end MirandaDynamics
end HeytingLean
