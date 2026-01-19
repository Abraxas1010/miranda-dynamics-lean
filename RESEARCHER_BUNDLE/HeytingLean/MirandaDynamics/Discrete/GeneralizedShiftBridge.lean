import HeytingLean.MirandaDynamics.Discrete.HaltingToPeriodic
import HeytingLean.MirandaDynamics.Discrete.HaltSys
import HeytingLean.MirandaDynamics.Computation.GeneralizedShiftPeriodic

/-!
# MirandaDynamics.Discrete: periodic-orbit reachability inside a generalized shift (WS5+)

This file packages an internal, fully mechanized “symbolic dynamics” consequence:

* The discrete halting ↔ reach-a-period-2-orbit reduction can be transported into the generalized
  shift embedding of that discrete system.

This is a concrete mechanizable stepping stone for the long-horizon Reeb/Beltrami/Euler
realization theorems: the analytic work can target *this* generalized-shift dynamical predicate.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Discrete

open Nat.Partrec
open Nat.Partrec.Code

namespace ShiftPeriodic

open HeytingLean.MirandaDynamics.Computation

noncomputable section

noncomputable def shiftStep (n : Nat) (c : Code) : GenShiftCfg (Option State) → GenShiftCfg (Option State) :=
  GenShiftRule.step (Embed.rule (M := HaltSysBridge.sys n c))

noncomputable def startCfg : GenShiftCfg (Option State) :=
  Embed.embedCfg (Cfg := State) start

def ReachesPeriod2Shift (n : Nat) (c : Code) : Prop :=
  ∃ t : Nat, Function.IsPeriodicPt (shiftStep n c) 2 ((shiftStep n c)^[t] startCfg)

theorem reachesPeriod2Shift_iff_reachesPeriod2 (n : Nat) (c : Code) :
    ReachesPeriod2Shift n c ↔ ReachesPeriod2 n c := by
  constructor
  · rintro ⟨t, ht⟩
    -- Rewrite the orbit inside the generalized shift as an embedded orbit of the discrete system.
    have hOrbit :
        (shiftStep n c)^[t] startCfg =
          Embed.embedCfg (Cfg := State) ((step n c)^[t] start) := by
      simpa [shiftStep, startCfg] using
        (Embed.iterate_step_embedCfg (M := HaltSysBridge.sys n c) t start)
    refine ⟨t, ?_⟩
    -- Transport periodicity through `embedCfg`, then cancel it using injectivity.
    have ht' :
        Embed.embedCfg (Cfg := State) ((step n c)^[t] start) =
          (shiftStep n c)^[2] (Embed.embedCfg (Cfg := State) ((step n c)^[t] start)) := by
      -- `ht` is periodicity for the LHS point; rewrite it via `hOrbit`.
      have : (shiftStep n c)^[2] ((shiftStep n c)^[t] startCfg) = (shiftStep n c)^[t] startCfg := by
        simpa [Function.IsPeriodicPt, Function.IsFixedPt] using ht
      -- Put the orbit in embedded form and rearrange.
      simpa [hOrbit] using this.symm
    -- Rewrite the RHS using the iterate commutation lemma, then cancel with tape-injectivity.
    have h2 :
        (shiftStep n c)^[2] (Embed.embedCfg (Cfg := State) ((step n c)^[t] start)) =
          Embed.embedCfg (Cfg := State) ((step n c)^[2] ((step n c)^[t] start)) := by
      simpa [shiftStep] using
        (Embed.iterate_step_embedCfg (M := HaltSysBridge.sys n c) 2 ((step n c)^[t] start))
    have hEq :
        Embed.embedCfg (Cfg := State) ((step n c)^[t] start) =
          Embed.embedCfg (Cfg := State) ((step n c)^[2] ((step n c)^[t] start)) := by
      simpa [h2] using ht'
    -- `embedCfg` is injective because its tape has `some c` at index 0.
    have hTape :
        Embed.embedTape (Cfg := State) ((step n c)^[t] start) =
          Embed.embedTape (Cfg := State) ((step n c)^[2] ((step n c)^[t] start)) := by
      simpa [Embed.embedCfg] using congrArg GenShiftCfg.tape hEq
    have h0 :
        (Embed.embedTape (Cfg := State) ((step n c)^[t] start)) 0 =
          (Embed.embedTape (Cfg := State) ((step n c)^[2] ((step n c)^[t] start))) 0 := by
      simpa using congrArg (fun tt => tt 0) hTape
    have hsome : (some ((step n c)^[t] start) : Option State) = some ((step n c)^[2] ((step n c)^[t] start)) := by
      simpa [Embed.embedTape] using h0
    have hStateEq : (step n c)^[t] start = (step n c)^[2] ((step n c)^[t] start) :=
      Option.some.inj hsome
    simpa [Function.IsPeriodicPt, Function.IsFixedPt] using hStateEq.symm
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    -- The orbit point in the generalized shift is an embedding of the orbit point in the discrete system.
    have hOrbit :
        (shiftStep n c)^[t] startCfg =
          Embed.embedCfg (Cfg := State) ((step n c)^[t] start) := by
      simpa [shiftStep, startCfg] using
        (Embed.iterate_step_embedCfg (M := HaltSysBridge.sys n c) t start)
    -- Apply periodicity after embedding and rewrite with the iterate commutation lemma.
    have ht' :
        Embed.embedCfg (Cfg := State) ((step n c)^[2] ((step n c)^[t] start)) =
          Embed.embedCfg (Cfg := State) ((step n c)^[t] start) := by
      -- `ht` is periodicity for the discrete point.
      have hEq : (step n c)^[2] ((step n c)^[t] start) = (step n c)^[t] start := by
        simpa [Function.IsPeriodicPt, Function.IsFixedPt] using ht
      simpa using congrArg (fun s => Embed.embedCfg (Cfg := State) s) hEq
    have h2 :
        (shiftStep n c)^[2] (Embed.embedCfg (Cfg := State) ((step n c)^[t] start)) =
          Embed.embedCfg (Cfg := State) ((step n c)^[2] ((step n c)^[t] start)) := by
      simpa [shiftStep] using
        (Embed.iterate_step_embedCfg (M := HaltSysBridge.sys n c) 2 ((step n c)^[t] start))
    -- Conclude periodicity of the generalized-shift point.
    have : (shiftStep n c)^[2] ((shiftStep n c)^[t] startCfg) = (shiftStep n c)^[t] startCfg := by
      simpa [hOrbit, h2] using ht'
    simpa [Function.IsPeriodicPt, Function.IsFixedPt] using this

theorem reachesPeriod2Shift_iff_halting (n : Nat) (c : Code) :
    ReachesPeriod2Shift n c ↔ Undecidability.Halting.Halts n c := by
  simpa [reachesPeriod2Shift_iff_reachesPeriod2] using (reachesPeriod2_iff_halts n c)

/-! ## Many-one reduction + non-computability consequence -/

/-- In the generalized-shift embedding, halting many-one reduces to reaching a period-2 orbit. -/
def haltingReducesToReachesPeriod2Shift (n : Nat) :
    Undecidability.ManyOne (p := Undecidability.Halting.Halts n) (q := fun c : Code => ReachesPeriod2Shift n c) where
  f := id
  computable_f := Computable.id
  correct := fun c => (reachesPeriod2Shift_iff_halting n c).symm

theorem not_computable_reachesPeriod2Shift (n : Nat) :
    ¬ComputablePred (fun c : Code => ReachesPeriod2Shift n c) :=
  Undecidability.Halting.not_computable_of_halting_reduces (n := n) (haltingReducesToReachesPeriod2Shift n)

end

end ShiftPeriodic

end Discrete
end MirandaDynamics
end HeytingLean
