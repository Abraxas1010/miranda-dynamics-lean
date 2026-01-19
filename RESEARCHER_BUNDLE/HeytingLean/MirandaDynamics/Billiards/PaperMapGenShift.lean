import HeytingLean.MirandaDynamics.Billiards.CantorDigits
import HeytingLean.MirandaDynamics.Billiards.PaperMap
import HeytingLean.MirandaDynamics.Computation.GeneralizedShift

/-!
# MirandaDynamics.Billiards: paper map as a realization of a generalized shift (WS7.4 ↔ WS5+)

This file packages a clean “symbolic dynamics” statement:

* The Cantor/head encoding
  `encodeCfg (t, k) = (encodeTape t, encodeWithHead t k)`
  conjugates a generalized-shift step on `(Tape, head)` to an explicit partial map on `ℝ²`.

We define `paperFgen?` parameterized by a local rule

* `next : Bool → Bool × ℤ`

and prove that on encoded configurations it performs exactly the corresponding write + head-move.

This is an important mechanizable bridge: the long-horizon billiards construction can target the
generalized shift model from `Computation/GeneralizedShift.lean`, while the WS7.4 paper map gives a
concrete analytic (piecewise-affine) representative on a Cantor invariant set.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open HeytingLean.MirandaDynamics.Computation
open Set

/-- View a tape/head pair as a generalized-shift configuration (same data, different namespace). -/
def toGenShiftCfg (t : Tape) (k : ℤ) : GenShiftCfg Bool :=
  { tape := t
    head := k }

theorem tapeUpdate_eq_write (t : Tape) (k : ℤ) (b : Bool) :
    Computation.tapeUpdate t k b = Tape.write t k b := by
  funext z
  by_cases hz : z = k
  · subst hz
    simp [Computation.tapeUpdate, Tape.write]
  · simp [Computation.tapeUpdate, Tape.write, hz]

/-- The Cantor/head encoding of a generalized-shift configuration into `ℝ²`. -/
def encodeCfg (c : GenShiftCfg Bool) : ℝ × ℝ :=
  (encodeTape c.tape, encodeWithHead c.tape c.head)

/-- An explicit paper-style partial map on `ℝ²` corresponding to a generalized-shift local rule.

It reads the current head digit from the Cantor coordinate, updates that digit, and moves the head
by `dh` via `tau (k + dh)`. -/
def paperFgen? (next : Bool → Bool × ℤ) : (ℝ × ℝ) → Option (ℝ × ℝ)
  | (x, z) =>
      match headIndex? z with
      | none => none
      | some k =>
          match cantorDigitAt? (indexNat k) x with
          | none => none
          | some cur =>
              let out := next cur
              let b := out.1
              let dh := out.2
              let x' := x + writeDelta k b cur
              some (x', tau (k + dh) x')

theorem paperFgen?_encodeCfg (next : Bool → Bool × ℤ) (t : Tape) (k : ℤ) :
    paperFgen? next (encodeCfg (toGenShiftCfg t k)) =
      some (encodeCfg (GenShiftRule.step (α := Bool) ⟨next⟩ (toGenShiftCfg t k))) := by
  classical
  -- Unfold the encodings and evaluate the decoders on encoded points.
  have hz : encodeWithHead t k ∈ headInterval k :=
    tau_mem_headInterval (k := k) (x := encodeTape t) (encodeTape_mem_Icc t)
  have hk : headIndex? (encodeWithHead t k) = some k :=
    headIndex?_eq_some_of_mem (z := encodeWithHead t k) (k := k) hz
  have hkτ : headIndex? (tau k (encodeTape t)) = some k := by
    simpa [encodeWithHead] using hk
  have hcur : cantorDigitAt? (indexNat k) (encodeTape t) = some (t k) :=
    cantorDigitAt?_encodeTape_indexNat (t := t) (k := k)
  let b : Bool := (next (t k)).1
  let dh : ℤ := (next (t k)).2
  have hxWrite :
      encodeTape (Tape.write t k b) =
        encodeTape t + writeDelta k b (t k) := by
    simpa [b, writeDelta] using (encodeTape_write_eq_add_pow (t := t) (k := k) (b := b))
  -- Compute both sides and use the affine `encodeTape` update together with `encodeWithHead = tau ∘ encodeTape`.
  simp [paperFgen?, encodeCfg, toGenShiftCfg, hkτ, hcur, GenShiftRule.step, b, tapeUpdate_eq_write, hxWrite,
    encodeWithHead]

end Billiards
end MirandaDynamics
end HeytingLean
