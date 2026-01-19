import HeytingLean.MirandaDynamics.Billiards.GeometryToPaperTarget
import HeytingLean.MirandaDynamics.Billiards.PaperMapFiniteControlConjugacy
import HeytingLean.MirandaDynamics.Billiards.PartialMapIterate

/-!
# MirandaDynamics.Billiards: a concrete PaperLink on the paper cross-section (symbolic model)

The long-horizon WS7.3 goal is to construct a billiard table + cross-section whose **return map**
is semiconjugate to the WS7.4 paper map `paperFctrl?`.

This file implements the closest fully mechanizable intermediate:

* take the cross-section state space to be the **controlled generalized shift configuration**
  `GenShiftCtrlCfg (Fin m) Bool`,
* take the “next” map to be the shift step (total, hence `Option`-wrapped),
* take the encoding to the WS7.4 plane to be `encodeCfgCtrl`,
* prove the one-step semiconjugacy using the already-mechanized WS7.4 conjugacy.

This does **not** yet build the geometric billiard table; it provides the exact `encode`/`semiconj`
statement that the geometry proof must eventually realize.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set
open HeytingLean.MirandaDynamics.Computation

namespace GenShiftCtrlMap

variable {m : ℕ} (next : Fin m → Bool → Fin m × Bool × ℤ)

/-- The controlled generalized-shift “next” step as a partial deterministic map. -/
def next? (cfg : GenShiftCtrlCfg (Fin m) Bool) : Option (GenShiftCtrlCfg (Fin m) Bool) :=
  some (GenShiftCtrlRule.step (Q := Fin m) (α := Bool) ⟨next⟩ cfg)

@[simp] theorem next?_eq_some (cfg : GenShiftCtrlCfg (Fin m) Bool) :
    next? (m := m) next cfg =
      some (GenShiftCtrlRule.step (Q := Fin m) (α := Bool) ⟨next⟩ cfg) := rfl

/-- Encoded configurations always lie in the WS7.4 branch domain. -/
theorem encodeCfgCtrl_mem_CtrlDomain (hm : 0 < m) (cfg : GenShiftCtrlCfg (Fin m) Bool) :
    encodeCfgCtrl (m := m) cfg ∈ CtrlDomain m := by
  classical
  refine ⟨cfg.head, cfg.state, cfg.tape cfg.head, ?_⟩
  cases cfg with
  | mk q t k =>
    simpa [encodeCfgCtrl, toGenShiftCtrlCfg] using
      (encodeCfgCtrl_mem_CtrlCantorBlock (m := m) hm t k q)

/-- One-step semiconjugacy (symbolic shift → paper map) on all states. -/
theorem semiconj (hm : 0 < m) (cfg : GenShiftCtrlCfg (Fin m) Bool) :
    Option.map (encodeCfgCtrl (m := m)) (next? (m := m) next cfg) =
      paperFctrl? next (encodeCfgCtrl (m := m) cfg) := by
  simp [next?, paperFctrl?_encodeCfgCtrl_cfg (m := m) hm (next := next)]

/-- A concrete `UnitSquareMap.PaperLink`-shaped package for the WS7.4 semiconjugacy,
but on the symbolic cross-section state space.

This is the target that the geometry construction must eventually factor through. -/
structure PaperLink (m : ℕ) (next : Fin m → Bool → Fin m × Bool × ℤ) where
  encode : GenShiftCtrlCfg (Fin m) Bool → ℝ × ℝ
  encode_mem : ∀ cfg, encode cfg ∈ CtrlDomain m
  semiconj : ∀ cfg, Option.map encode (next? (m := m) next cfg) = paperFctrl? next (encode cfg)

def paperLink (hm : 0 < m) : PaperLink m next :=
  { encode := encodeCfgCtrl (m := m)
    encode_mem := fun cfg => encodeCfgCtrl_mem_CtrlDomain (m := m) hm cfg
    semiconj := fun cfg => semiconj (m := m) (next := next) hm cfg }

/-! ## Iteration / return lifting -/

theorem semiconj_iter (hm : 0 < m) (n : Nat) (cfg : GenShiftCtrlCfg (Fin m) Bool) :
    Option.map (encodeCfgCtrl (m := m)) (iter? (next? (m := m) next) n cfg) =
      iter? (paperFctrl? next) n (encodeCfgCtrl (m := m) cfg) := by
  exact
    iter?_map_semiconj (f := next? (m := m) next) (g := paperFctrl? next)
      (encode := encodeCfgCtrl (m := m)) (hstep := fun a => (semiconj (m := m) (next := next) hm a)) n cfg

theorem ReturnRel_encode
    (hm : 0 < m)
    (S : GenShiftCtrlCfg (Fin m) Bool → Prop)
    (T : (ℝ × ℝ) → Prop)
    (hST : ∀ cfg, S cfg → T (encodeCfgCtrl (m := m) cfg)) :
    ∀ {a b : GenShiftCtrlCfg (Fin m) Bool},
      ReturnRel (next? (m := m) next) S a b →
        ReturnRel (paperFctrl? next) T (encodeCfgCtrl (m := m) a) (encodeCfgCtrl (m := m) b) := by
  intro a b hret
  -- `ReturnRel.map` applies since the semiconjugacy is global in this symbolic model.
  exact
    ReturnRel.map (f := next? (m := m) next) (g := paperFctrl? next)
      (encode := encodeCfgCtrl (m := m)) (S := S) (T := T)
      (hstep := fun a => semiconj (m := m) (next := next) hm a) (hST := hST) hret

end GenShiftCtrlMap

end Billiards
end MirandaDynamics
end HeytingLean
