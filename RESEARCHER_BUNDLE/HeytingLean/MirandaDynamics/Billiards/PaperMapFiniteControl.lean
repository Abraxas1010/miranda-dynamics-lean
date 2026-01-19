import HeytingLean.MirandaDynamics.Billiards.HeadStateEncoding
import HeytingLean.MirandaDynamics.Billiards.CantorDigits
import HeytingLean.MirandaDynamics.Billiards.PaperMap
import HeytingLean.MirandaDynamics.Computation.GeneralizedShiftControl

/-!
# MirandaDynamics.Billiards: paper map with finite control (WS7.4 ↔ WS5+)

This file extends the generalized paper map bridge `paperFgen?` by adding a finite control state
carried in the head coordinate (via `HeadStateEncoding.lean`).

Mechanized outcome:
* a controlled generalized shift step (`Computation.GenShiftCtrlRule.step`) is conjugated to an
  explicit partial map on `ℝ²` that is piecewise affine once `(k,q,cur)` are fixed.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set
open HeytingLean.MirandaDynamics.Computation

/-- View tape/head/state as a controlled generalized-shift configuration. -/
def toGenShiftCtrlCfg {m : ℕ} (t : Tape) (k : ℤ) (q : Fin m) : GenShiftCtrlCfg (Fin m) Bool :=
  { state := q
    tape := t
    head := k }

theorem tapeUpdate_eq_write (t : Tape) (k : ℤ) (b : Bool) :
    Computation.tapeUpdate t k b = Tape.write t k b := by
  funext z
  by_cases hz : z = k
  · subst hz
    simp [Computation.tapeUpdate, Tape.write]
  · simp [Computation.tapeUpdate, Tape.write, hz]

/-- Encode a controlled generalized-shift configuration into `ℝ²`. -/
def encodeCfgCtrl {m : ℕ} (c : GenShiftCtrlCfg (Fin m) Bool) : ℝ × ℝ :=
  (encodeTape c.tape, encodeWithHeadState m c.tape c.head c.state)

/-- A paper-style partial map on `ℝ²` for a controlled local rule.

It decodes `(k,q)` from the head coordinate, reads the `k`-th Cantor digit, performs the update,
and re-encodes the new `(k+dh,q')` in the head coordinate. -/
def paperFctrl? {m : ℕ} (next : Fin m → Bool → Fin m × Bool × ℤ) : (ℝ × ℝ) → Option (ℝ × ℝ)
  | (x, z) =>
      match headIndexState? m z with
      | none => none
      | some kq =>
          let k := kq.1
          let q := kq.2
          match cantorDigitAt? (indexNat k) x with
          | none => none
          | some cur =>
              let out := next q cur
              let q' := out.1
              let b := out.2.1
              let dh := out.2.2
              let x' := x + writeDelta k b cur
              some (x', tauState m (k + dh) q' x')

theorem paperFctrl?_encodeCfgCtrl {m : ℕ} (hm : 0 < m) (next : Fin m → Bool → Fin m × Bool × ℤ)
    (t : Tape) (k : ℤ) (q : Fin m) :
    paperFctrl? next (encodeCfgCtrl (toGenShiftCtrlCfg t k q)) =
      some (encodeCfgCtrl (GenShiftCtrlRule.step (Q := Fin m) (α := Bool) ⟨next⟩ (toGenShiftCtrlCfg t k q))) := by
  classical
  -- Unfold the encodings and evaluate the decoders on encoded points.
  have hkq : headIndexState? m (encodeWithHeadState m t k q) = some (k, q) :=
    headIndexState?_encodeWithHeadState (m := m) hm t k q
  have hkqτ : headIndexState? m (tauState m k q (encodeTape t)) = some (k, q) := by
    simpa [encodeWithHeadState] using hkq
  have hcur : cantorDigitAt? (indexNat k) (encodeTape t) = some (t k) :=
    cantorDigitAt?_encodeTape_indexNat (t := t) (k := k)
  let out := next q (t k)
  let b : Bool := out.2.1
  have hxWrite :
      encodeTape (Tape.write t k b) =
        encodeTape t + writeDelta k b (t k) := by
    simpa [writeDelta] using (encodeTape_write_eq_add_pow (t := t) (k := k) (b := b))
  -- Compute the map and rewrite with the tape/head update formulas.
  simp [paperFctrl?, encodeCfgCtrl, toGenShiftCtrlCfg, hkqτ, hcur, GenShiftCtrlRule.step, out, b,
    tapeUpdate_eq_write, hxWrite, encodeWithHeadState]

end Billiards
end MirandaDynamics
end HeytingLean
