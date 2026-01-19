import HeytingLean.MirandaDynamics.Billiards.GeometryToGenShiftCtrlLink
import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteTableCanonical

/-!
# MirandaDynamics.Billiards: WS7.3 return-map decode-step goal (staged)

The remaining WS7.3 geometry work is to build a **geometric** collision cross-section and a
deterministic return map whose dynamics simulates one step of the *controlled generalized shift*.

`PaperReadWriteTableCanonical.lean` already provides a canonical staged table boundary union and a
collision-space `CollisionState` with a deterministic minimal-time `next?` (via
`Table.DeterministicNext.next?`).

`GeometryToGenShiftCtrlLink.lean` shows that, once we have a decoding map into
`GenShiftCtrlCfg (Fin m) Bool` satisfying the `decode_step` commuting square on a proved `Good`
set, semiconjugacy to the paper map `paperFctrl?` follows automatically.

This file packages that remaining WS7.3 obligation as a concrete record over the staged
`PaperReadWriteTableCanonical.CollisionState`, so the exact target can be implemented and checked
incrementally without changing any existing geometry code.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open HeytingLean.MirandaDynamics.Computation

namespace WS73

open PaperReadWriteTableCanonical
open GeometryToGenShiftCtrl

variable {m : ℕ} (next : Fin m → Bool → Fin m × Bool × ℤ)

/--
WS7.3 target for the staged canonical read–write table:
provide a `decode` into controlled generalized shift configurations such that decoding commutes
with one `next?` step on `Good` collision states.

This is the exact hypothesis needed to instantiate `GeometryToGenShiftCtrl.Link` and obtain a
`PaperLink` semiconjugacy theorem to `paperFctrl?`.
-/
structure DecodeGoal where
  decode : CollisionState → GenShiftCtrlCfg (Fin m) Bool
  decode_step :
    ∀ s : CollisionState,
      Good s → Option.map decode (PaperReadWriteTableCanonical.next? s) =
        GenShiftCtrlMap.next? (m := m) next (decode s)

namespace DecodeGoal

variable {next}

/-- View a `DecodeGoal` as a `GeometryToGenShiftCtrl.Link` for the staged canonical table. -/
def toLink (g : DecodeGoal (m := m) next) :
    GeometryToGenShiftCtrl.Link CollisionState m next :=
  { Good := Good
    next? := PaperReadWriteTableCanonical.next?
    decode := g.decode
    decode_step := g.decode_step }

/-- The induced `PaperLink` semiconjugacy package (to `paperFctrl?`) once `DecodeGoal` is supplied. -/
def paperLink (g : DecodeGoal (m := m) next) (hm : 0 < m) : Billiards.PaperLink CollisionState m next :=
  GeometryToGenShiftCtrl.Link.paperLink (α := CollisionState) (m := m) (next := next) (g.toLink) hm

end DecodeGoal

end WS73

end Billiards
end MirandaDynamics
end HeytingLean

