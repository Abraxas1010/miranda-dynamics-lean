import HeytingLean.MirandaDynamics.Billiards.CantorEncoding

/-!
# MirandaDynamics.Billiards: extracting ternary Cantor digits from the tape encoding (WS7.4)

`CantorEncoding.lean` defines `cantorEncode : (ℕ → Bool) → ℝ` and proves a one-step recursion
(`cantorEncode_succ`). This file inverts that recursion to *read back* digits:

* `cantorHeadDigit? : ℝ → Option Bool` reads the leading `{0,2}` ternary digit (as `Bool`)
  using the interval split `[0,1/3] ∪ [2/3,1]`.
* `cantorTail? : ℝ → Option ℝ` computes the tail coordinate (multiply by 3, optionally subtract 2).
* `cantorDigitAt? n x` reads the `n`-th digit (0-based) when defined.

On points of the form `cantorEncode f` (and in particular `encodeTape t`), these decoders succeed
and return the expected digits. This supplies the “piecewise” digit-reading needed to remove the
classical-choice decoder from the WS7.4 paper map.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set

noncomputable section

/-! ## One-step digit and tail extraction -/

/-- The constant `1/3`, used as a cutoff in Cantor digit decoding. -/
noncomputable def oneThird : ℝ := ((3 : ℝ)⁻¹)

/-- The constant `2/3`, used as a cutoff in Cantor digit decoding. -/
noncomputable def twoThird : ℝ := (2 : ℝ) * ((3 : ℝ)⁻¹)

noncomputable def cantorHeadDigit? (x : ℝ) : Option Bool :=
  if x ≤ oneThird then
    some false
  else if twoThird ≤ x then
    some true
  else
    none

noncomputable def cantorTail? (x : ℝ) : Option ℝ :=
  match cantorHeadDigit? x with
  | some false => some (3 * x)
  | some true => some (3 * x - 2)
  | none => none

theorem cantorHeadDigit?_cantorEncode (f : ℕ → Bool) :
    cantorHeadDigit? (cantorEncode f) = some (f 0) := by
  classical
  -- Let `tail = cantorEncode (fun n => f (n+1))`.
  set tail : ℝ := cantorEncode (fun n => f (n + 1))
  have htail : tail ∈ Set.Icc (0 : ℝ) 1 := cantorEncode_mem_Icc (fun n => f (n + 1))
  have hs : cantorEncode f =
      (if f 0 then (2 + tail) / 3 else tail / 3) := by
    -- Use `cantorEncode_succ` at this specific `f` (avoids simp loops).
    simp [tail, cantorEncode_succ (f := f)]
  by_cases h : f 0
  · -- Leading digit = 2, so `x = (2+tail)/3 ∈ [2/3, 1]`.
    have hx : cantorEncode f = (2 + tail) / 3 := by simp [hs, h]
    have hge : twoThird ≤ cantorEncode f := by
      have h0 : (0 : ℝ) ≤ tail := htail.1
      have hnum : (2 : ℝ) ≤ 2 + tail := by linarith
      have hdiv : (2 : ℝ) / 3 ≤ (2 + tail) / 3 :=
        div_le_div_of_nonneg_right hnum (by linarith : (0 : ℝ) ≤ 3)
      have : twoThird ≤ (2 + tail) / 3 := by
        simpa [twoThird, one_div] using hdiv
      simpa [hx] using this
    -- Evaluate the `if`-split: the `≤ 1/3` branch is impossible since `2/3 ≤ x`.
    unfold cantorHeadDigit?
    have hxne : ¬ cantorEncode f ≤ oneThird := by
      intro hxle
      have hcontra : ¬ twoThird ≤ oneThird := by
        norm_num [twoThird, oneThird]
      exact hcontra (hge.trans hxle)
    -- Now the second branch triggers.
    rw [if_neg hxne]
    simp [hge, h]
  · -- Leading digit = 0, so `x = tail/3 ∈ [0, 1/3]`.
    have hx : cantorEncode f = tail / 3 := by simp [hs, h]
    have hle : cantorEncode f ≤ oneThird := by
      have ht : tail ≤ (1 : ℝ) := htail.2
      have : tail / 3 ≤ oneThird := by
        have : tail / 3 ≤ (1 : ℝ) / 3 :=
          div_le_div_of_nonneg_right ht (by linarith : (0 : ℝ) ≤ 3)
        simp [one_div] at this
        exact this
      simpa [hx] using this
    unfold cantorHeadDigit?
    rw [if_pos hle]
    simp [h]

theorem cantorTail?_cantorEncode (f : ℕ → Bool) :
    cantorTail? (cantorEncode f) = some (cantorEncode (fun n => f (n + 1))) := by
  classical
  set tail : ℝ := cantorEncode (fun n => f (n + 1))
  have htail : tail ∈ Set.Icc (0 : ℝ) 1 := cantorEncode_mem_Icc (fun n => f (n + 1))
  have hs : cantorEncode f =
      (if f 0 then (2 + tail) / 3 else tail / 3) := by
    simp [tail, cantorEncode_succ (f := f)]
  by_cases h : f 0
  · have hx : cantorEncode f = (2 + tail) / 3 := by simp [hs, h]
    have hge : twoThird ≤ cantorEncode f := by
      have h0 : (0 : ℝ) ≤ tail := htail.1
      have hnum : (2 : ℝ) ≤ 2 + tail := by linarith
      have hdiv : (2 : ℝ) / 3 ≤ (2 + tail) / 3 :=
        div_le_div_of_nonneg_right hnum (by linarith : (0 : ℝ) ≤ 3)
      have : twoThird ≤ (2 + tail) / 3 := by
        simpa [twoThird, one_div] using hdiv
      simpa [hx] using this
    unfold cantorTail? cantorHeadDigit?
    have hxne : ¬ cantorEncode f ≤ oneThird := by
      intro hxle
      have hcontra : ¬ twoThird ≤ oneThird := by
        norm_num [twoThird, oneThird]
      exact hcontra (hge.trans hxle)
    rw [if_neg hxne]
    have hcalc : 3 * cantorEncode f - 2 = tail := by
      simp [hx]
      ring_nf
    simp [hge, hcalc, tail]
  · have hx : cantorEncode f = tail / 3 := by simp [hs, h]
    have hle : cantorEncode f ≤ oneThird := by
      have ht : tail ≤ (1 : ℝ) := htail.2
      have : tail / 3 ≤ oneThird := by
        have : tail / 3 ≤ (1 : ℝ) / 3 :=
          div_le_div_of_nonneg_right ht (by linarith : (0 : ℝ) ≤ 3)
        simp [one_div] at this
        exact this
      simpa [hx] using this
    unfold cantorTail? cantorHeadDigit?
    rw [if_pos hle]
    have hcalc : 3 * cantorEncode f = tail := by
      simp [hx]
      ring_nf
    simp [hcalc, tail]

/-! ## Iterated digit extraction -/

noncomputable def cantorDigitAt? : Nat → ℝ → Option Bool
  | 0, x => cantorHeadDigit? x
  | n + 1, x =>
      match cantorTail? x with
      | some x' => cantorDigitAt? n x'
      | none => none

theorem cantorDigitAt?_cantorEncode (f : ℕ → Bool) (n : Nat) :
    cantorDigitAt? n (cantorEncode f) = some (f n) := by
  induction n generalizing f with
  | zero =>
    simp [cantorDigitAt?, cantorHeadDigit?_cantorEncode]
  | succ n ih =>
    have htail : cantorTail? (cantorEncode f) = some (cantorEncode (fun m => f (m + 1))) :=
      cantorTail?_cantorEncode f
    -- After one tail step we apply the induction hypothesis to the shifted stream.
    simpa [cantorDigitAt?, htail] using (ih (f := fun m => f (m + 1)))

theorem cantorDigitAt?_encodeTape (t : Tape) (n : Nat) :
    cantorDigitAt? n (encodeTape t) = some (digits t n) := by
  simpa [encodeTape] using (cantorDigitAt?_cantorEncode (f := digits t) n)

theorem cantorDigitAt?_encodeTape_indexNat (t : Tape) (k : ℤ) :
    cantorDigitAt? (indexNat k) (encodeTape t) = some (t k) := by
  have := cantorDigitAt?_encodeTape (t := t) (n := indexNat k)
  simpa [digits, tapeIndex_indexNat] using this

end

end Billiards
end MirandaDynamics
end HeytingLean
