import HeytingLean.MirandaDynamics.Billiards.PaperMap

/-!
# MirandaDynamics.Billiards: a “full” paper-level map on the Cantor/head invariant set (WS7.4)

`PaperMap.lean` defines a shift-only skeleton (`paperF?`) and a “write + shift” fragment
(`paperWriteF?`) that still takes the current digit as an explicit parameter.

This file removes that extra parameter by adding a *partial decoder* for the tape coordinate:

* `decodeTape? : ℝ → Option Tape`, defined by classical choice on the image of `encodeTape`.

Using that decoder, we define a noncomputable partial map

* `paperFfull? (δ : Bool → Bool) : ℝ × ℝ → Option (ℝ × ℝ)`

that:
1) reads the head index `k` from the head coordinate `z`,
2) decodes the tape `t` from the Cantor coordinate `x`,
3) overwrites the head cell `k` by a local rule `δ` and shifts the head to `k+1`,
4) re-encodes into `ℝ²`.

On the encoded invariant set `(encodeTape t, encodeWithHead t k)`, this coincides with the
explicit piecewise-affine formulas from `paperWriteF?` via `encodeTape_write_eq_add_pow`.

No “real analysis” about decoding arbitrary Cantor points is claimed here: outside the image of
`encodeTape`, the map is simply undefined.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set

noncomputable def decodeTape? (x : ℝ) : Option Tape := by
  classical
  exact if h : ∃ t : Tape, encodeTape t = x then some (Classical.choose h) else none

theorem decodeTape?_eq_some_of_encodeTape (t : Tape) :
    decodeTape? (encodeTape t) = some t := by
  classical
  have h : ∃ t' : Tape, encodeTape t' = encodeTape t := ⟨t, rfl⟩
  have hchoose : encodeTape (Classical.choose h) = encodeTape t :=
    Classical.choose_spec h
  have ht : Classical.choose h = t := encodeTape_injective hchoose
  simp [decodeTape?, h, ht]

noncomputable def paperFfull? (δ : Bool → Bool) : (ℝ × ℝ) → Option (ℝ × ℝ)
  | (x, z) =>
      match headIndex? z, decodeTape? x with
      | some k, some t =>
          let cur := t k
          let b := δ cur
          let t' := Tape.write t k b
          some (encodeTape t', encodeWithHead t' (k + 1))
      | _, _ => none

theorem paperFfull?_encode_pair (δ : Bool → Bool) (t : Tape) (k : ℤ) :
    paperFfull? δ (encodeTape t, encodeWithHead t k) =
      some (encodeTape (Tape.write t k (δ (t k))), encodeWithHead (Tape.write t k (δ (t k))) (k + 1)) := by
  classical
  have hz : encodeWithHead t k ∈ headInterval k :=
    tau_mem_headInterval (k := k) (x := encodeTape t) (encodeTape_mem_Icc t)
  have hk : headIndex? (encodeWithHead t k) = some k :=
    headIndex?_eq_some_of_mem (z := encodeWithHead t k) (k := k) hz
  have ht : decodeTape? (encodeTape t) = some t :=
    decodeTape?_eq_some_of_encodeTape t
  simp [paperFfull?, hk, ht]

theorem paperFfull?_eq_paperWriteF?_on_encode (δ : Bool → Bool) (t : Tape) (k : ℤ) :
    paperFfull? δ (encodeTape t, encodeWithHead t k) =
      paperWriteF? (δ (t k)) (t k) (encodeTape t, encodeWithHead t k) := by
  -- Both sides compute to the same encoded successor pair.
  simp [paperFfull?_encode_pair, paperWriteF?_encode_pair]

theorem paperFfull?_affine_on_encode (δ : Bool → Bool) (t : Tape) (k : ℤ) :
    paperFfull? δ (encodeTape t, encodeWithHead t k) =
      some
        (encodeTape t + writeDelta k (δ (t k)) (t k),
          tau (k + 1) (encodeTape t + writeDelta k (δ (t k)) (t k))) := by
  -- Use the explicit affine write formula.
  have hx :
      encodeTape (Tape.write t k (δ (t k))) =
        encodeTape t + writeDelta k (δ (t k)) (t k) := by
    simpa [writeDelta] using (encodeTape_write_eq_add_pow (t := t) (k := k) (b := δ (t k)))
  -- Expand `paperFfull?` on encoded points and rewrite `encodeTape` of the updated tape.
  calc
    paperFfull? δ (encodeTape t, encodeWithHead t k) =
        some (encodeTape (Tape.write t k (δ (t k))), encodeWithHead (Tape.write t k (δ (t k))) (k + 1)) := by
          simp [paperFfull?_encode_pair]
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
