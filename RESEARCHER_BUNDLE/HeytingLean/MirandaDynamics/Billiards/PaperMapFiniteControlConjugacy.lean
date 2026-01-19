import HeytingLean.MirandaDynamics.Billiards.PaperMapFiniteControlBlocks

/-!
# MirandaDynamics.Billiards: full WS7.4 conjugacy (finite control, all branches)

`PaperMapFiniteControl.lean` proves the controlled-shift conjugacy on *encoded configurations*.
`PaperMapFiniteControlBlocks.lean` proves that `paperFctrl?` is *piecewise affine* on the branch
blocks `(k,q,cur)`.

This file ties those together:

* encoded configurations land in the corresponding control Cantor block,
* on encoded configurations, `paperFctrl?` selects the correct affine branch,
* that affine branch output equals the encoded controlled generalized-shift step.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set
open HeytingLean.MirandaDynamics.Computation

theorem encodeCfgCtrl_mem_CtrlCantorBlock {m : ℕ} (hm : 0 < m) (t : Tape) (k : ℤ) (q : Fin m) :
    encodeCfgCtrl (toGenShiftCtrlCfg t k q) ∈ CtrlCantorBlock m k q (t k) := by
  refine ⟨?_, ?_⟩
  · simpa [encodeCfgCtrl] using (encodeWithHeadState_mem_headStateInterval (m := m) hm t k q)
  · simpa [encodeCfgCtrl] using (cantorDigitAt?_encodeTape_indexNat (t := t) (k := k))

theorem paperFctrl?_eq_some_paperFctrlAffine_on_encodeCfgCtrl {m : ℕ} (hm : 0 < m)
    (next : Fin m → Bool → Fin m × Bool × ℤ) (t : Tape) (k : ℤ) (q : Fin m) :
    paperFctrl? next (encodeCfgCtrl (toGenShiftCtrlCfg t k q)) =
      some (paperFctrlAffine next k q (t k) (encodeCfgCtrl (toGenShiftCtrlCfg t k q))) := by
  have hmem : encodeCfgCtrl (toGenShiftCtrlCfg t k q) ∈ CtrlCantorBlock m k q (t k) :=
    encodeCfgCtrl_mem_CtrlCantorBlock (m := m) hm t k q
  simpa using
    (paperFctrl?_eq_some_paperFctrlAffine_of_mem (m := m) hm (next := next) (k := k) (q := q) (cur := t k)
      (p := encodeCfgCtrl (toGenShiftCtrlCfg t k q)) hmem)

theorem paperFctrlAffine_encodeCfgCtrl_eq_encodeCfgCtrl_step {m : ℕ} (hm : 0 < m)
    (next : Fin m → Bool → Fin m × Bool × ℤ) (t : Tape) (k : ℤ) (q : Fin m) :
    paperFctrlAffine next k q (t k) (encodeCfgCtrl (toGenShiftCtrlCfg t k q)) =
      encodeCfgCtrl (GenShiftCtrlRule.step (Q := Fin m) (α := Bool) ⟨next⟩ (toGenShiftCtrlCfg t k q)) := by
  have hAffine :
      paperFctrl? next (encodeCfgCtrl (toGenShiftCtrlCfg t k q)) =
        some (paperFctrlAffine next k q (t k) (encodeCfgCtrl (toGenShiftCtrlCfg t k q))) :=
    paperFctrl?_eq_some_paperFctrlAffine_on_encodeCfgCtrl (m := m) hm next t k q
  have hStep :
      paperFctrl? next (encodeCfgCtrl (toGenShiftCtrlCfg t k q)) =
        some
          (encodeCfgCtrl
            (GenShiftCtrlRule.step (Q := Fin m) (α := Bool) ⟨next⟩ (toGenShiftCtrlCfg t k q))) :=
    paperFctrl?_encodeCfgCtrl (m := m) hm next t k q
  have : some (paperFctrlAffine next k q (t k) (encodeCfgCtrl (toGenShiftCtrlCfg t k q))) =
      some
        (encodeCfgCtrl
          (GenShiftCtrlRule.step (Q := Fin m) (α := Bool) ⟨next⟩ (toGenShiftCtrlCfg t k q))) := by
    exact Eq.trans hAffine.symm hStep
  exact Option.some.inj this

theorem paperFctrl?_encodeCfgCtrl_cfg {m : ℕ} (hm : 0 < m)
    (next : Fin m → Bool → Fin m × Bool × ℤ) (cfg : GenShiftCtrlCfg (Fin m) Bool) :
    paperFctrl? next (encodeCfgCtrl cfg) =
      some (encodeCfgCtrl (GenShiftCtrlRule.step (Q := Fin m) (α := Bool) ⟨next⟩ cfg)) := by
  cases cfg with
  | mk q t k =>
    simpa [encodeCfgCtrl, toGenShiftCtrlCfg] using paperFctrl?_encodeCfgCtrl (m := m) hm next t k q

theorem paperFctrlAffine_encodeCfgCtrl_eq_encodeCfgCtrl_step_cfg {m : ℕ} (hm : 0 < m)
    (next : Fin m → Bool → Fin m × Bool × ℤ) (cfg : GenShiftCtrlCfg (Fin m) Bool) :
    paperFctrlAffine next cfg.head cfg.state (cfg.tape cfg.head) (encodeCfgCtrl cfg) =
      encodeCfgCtrl (GenShiftCtrlRule.step (Q := Fin m) (α := Bool) ⟨next⟩ cfg) := by
  cases cfg with
  | mk q t k =>
    simpa [encodeCfgCtrl, toGenShiftCtrlCfg] using
      paperFctrlAffine_encodeCfgCtrl_eq_encodeCfgCtrl_step (m := m) hm next t k q

end Billiards
end MirandaDynamics
end HeytingLean

