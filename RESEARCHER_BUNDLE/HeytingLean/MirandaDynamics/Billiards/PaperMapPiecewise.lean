import HeytingLean.MirandaDynamics.Billiards.PaperMap
import HeytingLean.MirandaDynamics.Billiards.CantorDigits

/-!
# MirandaDynamics.Billiards: a digit-reading paper map on the Cantor/head invariant set (WS7.4)

`PaperMapFull.lean` defines `paperFfull?` by decoding the tape coordinate via classical choice on
the image of `encodeTape`. This file replaces that decoder with an explicit *piecewise* digit
extraction (`CantorDigits.lean`):

* `cantorDigitAt? n x` reads the `n`-th Cantor digit whenever defined,
* on `x = encodeTape t`, it returns `digits t n` (and in particular `t k` at `n = indexNat k`).

Using that, we define a fully explicit partial map

* `paperFpiece? (δ : Bool → Bool) : ℝ × ℝ → Option (ℝ × ℝ)`

that reads the current head symbol from the Cantor coordinate (instead of taking it as a parameter
or decoding the whole tape), then performs the same “write + shift” affine update as `paperWriteF?`.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set

/-- A WS7.4 “paper map” variant that reads the current head digit from the Cantor coordinate via
`cantorDigitAt? (indexNat k)`. -/
def paperFpiece? (δ : Bool → Bool) : (ℝ × ℝ) → Option (ℝ × ℝ)
  | (x, z) =>
      match headIndex? z with
      | none => none
      | some k =>
          match cantorDigitAt? (indexNat k) x with
          | none => none
          | some cur =>
              let b := δ cur
              let x' := x + writeDelta k b cur
              some (x', tau (k + 1) x')

theorem paperFpiece?_eq_paperWriteF?_on_encode (δ : Bool → Bool) (t : Tape) (k : ℤ) :
    paperFpiece? δ (encodeTape t, encodeWithHead t k) =
      paperWriteF? (δ (t k)) (t k) (encodeTape t, encodeWithHead t k) := by
  classical
  have hz : encodeWithHead t k ∈ headInterval k :=
    tau_mem_headInterval (k := k) (x := encodeTape t) (encodeTape_mem_Icc t)
  have hk : headIndex? (encodeWithHead t k) = some k :=
    headIndex?_eq_some_of_mem (z := encodeWithHead t k) (k := k) hz
  have hcur : cantorDigitAt? (indexNat k) (encodeTape t) = some (t k) :=
    cantorDigitAt?_encodeTape_indexNat (t := t) (k := k)
  simp [paperFpiece?, hk, hcur, paperWriteF?, writeDelta]

theorem paperFpiece?_encode_pair (δ : Bool → Bool) (t : Tape) (k : ℤ) :
    paperFpiece? δ (encodeTape t, encodeWithHead t k) =
      some (encodeTape (Tape.write t k (δ (t k))), encodeWithHead (Tape.write t k (δ (t k))) (k + 1)) := by
  simpa [paperFpiece?_eq_paperWriteF?_on_encode] using
    (paperWriteF?_encode_pair (t := t) (k := k) (b := δ (t k)))

theorem paperFpiece?_affine_on_encode (δ : Bool → Bool) (t : Tape) (k : ℤ) :
    paperFpiece? δ (encodeTape t, encodeWithHead t k) =
      some
        (encodeTape t + writeDelta k (δ (t k)) (t k),
          tau (k + 1) (encodeTape t + writeDelta k (δ (t k)) (t k))) := by
  -- Combine the definitional formula with the explicit `encodeTape` write-affinity.
  have hx :
      encodeTape (Tape.write t k (δ (t k))) =
        encodeTape t + writeDelta k (δ (t k)) (t k) := by
    simpa [writeDelta] using (encodeTape_write_eq_add_pow (t := t) (k := k) (b := δ (t k)))
  calc
    paperFpiece? δ (encodeTape t, encodeWithHead t k) =
        some (encodeTape (Tape.write t k (δ (t k))), encodeWithHead (Tape.write t k (δ (t k))) (k + 1)) := by
          simp [paperFpiece?_encode_pair]
    _ =
        some (encodeTape t + writeDelta k (δ (t k)) (t k),
          encodeWithHead (Tape.write t k (δ (t k))) (k + 1)) := by
          simp [hx]
    _ =
        some (encodeTape t + writeDelta k (δ (t k)) (t k),
          tau (k + 1) (encodeTape (Tape.write t k (δ (t k))))) := by
          rfl
    _ =
        some (encodeTape t + writeDelta k (δ (t k)) (t k),
          tau (k + 1) (encodeTape t + writeDelta k (δ (t k)) (t k))) := by
          simp [hx]

end Billiards
end MirandaDynamics
end HeytingLean

