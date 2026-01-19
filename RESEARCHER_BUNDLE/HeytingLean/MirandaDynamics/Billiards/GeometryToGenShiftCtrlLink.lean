import HeytingLean.MirandaDynamics.Billiards.GenShiftCtrlPaperLink
import HeytingLean.MirandaDynamics.Billiards.PaperLinkGeneric

/-!
# MirandaDynamics.Billiards: glue lemma from geometric return maps to `paperFctrl?` (WS7.3 → WS7.4)

The long-horizon WS7.3 geometry task is to construct a genuine billiard table + collision
cross-section whose **return map** is semiconjugate to the WS7.4 paper map `paperFctrl?`.

The repo already contains a fully mechanized semiconjugacy for the *controlled generalized shift*
model (`GenShiftCtrlPaperLink.lean`). This file provides the missing **glue**:

If a geometric cross-section dynamics `(Good, next?)` admits a decoding map
`decode : α → GenShiftCtrlCfg (Fin m) Bool` such that `next?` simulates one generalized-shift step,
then semiconjugacy to `paperFctrl?` follows automatically by composition.

This reduces the remaining WS7.3 workload to supplying:
1. a geometric return map on a collision cross-section, and
2. a proof that it simulates the controlled generalized shift step on decoded configurations.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set
open HeytingLean.MirandaDynamics.Computation

namespace GeometryToGenShiftCtrl

open GenShiftCtrlMap

variable {α : Type} {m : ℕ} (next : Fin m → Bool → Fin m × Bool × ℤ)

/-- A *geometric* cross-section return map that decodes to a controlled generalized shift step. -/
structure Link (α : Type) (m : ℕ) (next : Fin m → Bool → Fin m × Bool × ℤ) where
  /-- Good states (exclude singularities/corners/tangencies in the future geometric layer). -/
  Good : α → Prop
  /-- The (partial) return map on the cross-section. -/
  next? : α → Option α
  /-- Decode a cross-section state to a controlled generalized-shift configuration. -/
  decode : α → GenShiftCtrlCfg (Fin m) Bool
  /-- Decoding commutes with the return map (one discrete step). -/
  decode_step :
    ∀ s : α, Good s → Option.map decode (next? s) = GenShiftCtrlMap.next? (m := m) next (decode s)

namespace Link

variable {next}

/-- Encode a geometric cross-section state into the WS7.4 plane via the decoded configuration. -/
def encode (link : Link α m next) : α → ℝ × ℝ :=
  fun s => encodeCfgCtrl (m := m) (link.decode s)

theorem encode_mem (link : Link α m next) (hm : 0 < m) (s : α) (hs : link.Good s) :
    link.encode (m := m) s ∈ CtrlDomain m :=
  GenShiftCtrlMap.encodeCfgCtrl_mem_CtrlDomain (m := m) (next := next) hm (link.decode s)

/-- One-step semiconjugacy to `paperFctrl?`, transported through `decode`. -/
theorem semiconj (link : Link α m next) (hm : 0 < m) (s : α) (hs : link.Good s) :
    Option.map (link.encode (m := m)) (link.next? s) =
      paperFctrl? next (link.encode (m := m) s) := by
  -- Rewrite the LHS as `Option.map encodeCfgCtrl` of the decoded-next, then use the already-proved
  -- semiconjugacy for the controlled generalized shift model.
  have hdecode :
      Option.map (encodeCfgCtrl (m := m)) (Option.map link.decode (link.next? s)) =
        Option.map (encodeCfgCtrl (m := m) ∘ link.decode) (link.next? s) := by
    simp [Function.comp]
  -- Use `decode_step` to replace the inner `Option.map decode (next? s)` with the shift step.
  calc
    Option.map (link.encode (m := m)) (link.next? s)
        = Option.map (encodeCfgCtrl (m := m) ∘ link.decode) (link.next? s) := by
            rfl
    _ = Option.map (encodeCfgCtrl (m := m)) (Option.map link.decode (link.next? s)) := by
          simpa [hdecode]
    _ = Option.map (encodeCfgCtrl (m := m)) (GenShiftCtrlMap.next? (m := m) next (link.decode s)) := by
          simpa using congrArg (Option.map (encodeCfgCtrl (m := m))) (link.decode_step s hs)
    _ = paperFctrl? next (encodeCfgCtrl (m := m) (link.decode s)) := by
          simpa using (GenShiftCtrlMap.semiconj (m := m) (next := next) hm (link.decode s))
    _ = paperFctrl? next (link.encode (m := m) s) := rfl

/-- Package the glue as an instance of the generic `PaperLink` interface. -/
def paperLink (link : Link α m next) (hm : 0 < m) : Billiards.PaperLink α m next :=
  { Good := link.Good
    next? := link.next?
    encode := link.encode (m := m)
    encode_mem := fun s hs => link.encode_mem (m := m) hm s hs
    semiconj := fun s hs => link.semiconj (m := m) hm s hs }

end Link

end GeometryToGenShiftCtrl

end Billiards
end MirandaDynamics
end HeytingLean

