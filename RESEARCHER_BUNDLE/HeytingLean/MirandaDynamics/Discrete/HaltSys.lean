import HeytingLean.MirandaDynamics.Computation.GeneralizedShift
import HeytingLean.MirandaDynamics.Computation.GeneralizedShiftControl
import HeytingLean.MirandaDynamics.Discrete.HaltingToPeriodic

/-!
# MirandaDynamics.Discrete: a `HaltSys` wrapper and generalized-shift simulation (WS5+)

This file wraps the fully mechanized discrete system from `Discrete/HaltingToPeriodic.lean` as a
`Computation.HaltSys`, then applies the generic generalized-shift embedding from
`Computation/GeneralizedShift.lean`.

The purpose is to provide a precise “symbolic dynamics” stepping stone:
halting-style dynamics → generalized shift → (later) billiards/fluids realizations.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Discrete

open Nat.Partrec
open Nat.Partrec.Code

open HeytingLean.MirandaDynamics

namespace HaltSysBridge

/-- Halting predicate for the discrete state: being on the 2-cycle branch. -/
def haltsState : State → Prop
  | Sum.inl _ => False
  | Sum.inr _ => True

/-- The discrete step system as a `Computation.HaltSys`. -/
def sys (n : Nat) (c : Code) : Computation.HaltSys State :=
  { step := step n c
    halts := haltsState }

theorem haltsState_iff_inr (s : State) : haltsState s ↔ ∃ b : Bool, s = Sum.inr b := by
  cases s <;> simp [haltsState]

theorem haltsFrom_start_iff_reachesPeriod2 (n : Nat) (c : Code) :
    (sys n c).haltsFrom start ↔ ReachesPeriod2 n c := by
  constructor
  · rintro ⟨t, ht⟩
    have hstepN : (sys n c).stepN t start = (step n c)^[t] start := by
      simpa [sys] using (Computation.HaltSys.stepN_eq_iterate (M := sys n c) t start)
    have ht0 : haltsState ((sys n c).stepN t start) := by
      simpa [Computation.HaltSys.haltsAt, sys] using ht
    have ht' : haltsState ((step n c)^[t] start) := by
      simpa [hstepN] using ht0
    rcases (haltsState_iff_inr ((step n c)^[t] start)).1 ht' with ⟨b, hb⟩
    refine ⟨t, ?_⟩
    simpa [hb] using periodic2_inr n c b
  · rintro ⟨t, htper⟩
    -- The reached state cannot be `inl _`, since those are not period-2.
    cases hstate : (step n c)^[t] start with
    | inl k =>
      exfalso
      have : ¬Function.IsPeriodicPt (step n c) 2 (Sum.inl k) := not_periodic2_inl n c k
      exact this (by simpa [hstate] using htper)
    | inr b =>
      refine ⟨t, ?_⟩
      have hstepN : (sys n c).stepN t start = (step n c)^[t] start := by
        simpa [sys] using (Computation.HaltSys.stepN_eq_iterate (M := sys n c) t start)
      have : haltsState ((step n c)^[t] start) := by
        simp [hstate, haltsState]
      have ht0 : haltsState ((sys n c).stepN t start) := by
        simpa [hstepN] using this
      -- Translate back to `haltsAt`.
      simpa [Computation.HaltSys.haltsAt, sys] using ht0

theorem haltsFrom_start_iff_halting (n : Nat) (c : Code) :
    (sys n c).haltsFrom start ↔ Undecidability.Halting.Halts n c := by
  -- Use the already-mechanized periodic-orbit bridge.
  simpa [haltsFrom_start_iff_reachesPeriod2] using (reachesPeriod2_iff_halts n c)

/-- The discrete `HaltSys` simulates into a generalized shift via the generic embedding. -/
def simRel (n : Nat) (c : Code) : State → Computation.GenShiftCfg (Option State) → Prop :=
  fun s cfg => Computation.Embed.Rel (sys n c) s cfg

theorem simRel_step (n : Nat) (c : Code) {s : State} {cfg : Computation.GenShiftCfg (Option State)}
    (h : simRel n c s cfg) :
    simRel n c ((sys n c).step s) (Computation.GenShiftRule.step (Computation.Embed.rule (M := sys n c)) cfg) :=
  by
    simpa [simRel] using (Computation.Embed.sim_step (M := sys n c) h)

theorem simRel_halts (n : Nat) (c : Code) {s : State} {cfg : Computation.GenShiftCfg (Option State)}
    (h : simRel n c s cfg) :
    ((sys n c).halts s ↔ (Computation.Embed.sys (M := sys n c)).halts cfg) :=
  by
    simpa [simRel] using (Computation.Embed.sim_halts (M := sys n c) h)

/-! ## Controlled generalized shift simulation (finite-control-friendly interface) -/

/-- The discrete `HaltSys` simulates into a controlled generalized shift that stores the whole
configuration as its control state. -/
def simRelCtrl (n : Nat) (c : Code) : State → Computation.GenShiftCtrlCfg State PUnit → Prop :=
  fun s cfg => Computation.ControlledEmbed.Rel (sys n c) s cfg

theorem simRelCtrl_step (n : Nat) (c : Code) {s : State} {cfg : Computation.GenShiftCtrlCfg State PUnit}
    (h : simRelCtrl n c s cfg) :
    simRelCtrl n c ((sys n c).step s)
      (Computation.GenShiftCtrlRule.step (Computation.ControlledEmbed.rule (M := sys n c)) cfg) := by
  simpa [simRelCtrl] using (Computation.ControlledEmbed.sim_step (M := sys n c) h)

theorem simRelCtrl_halts (n : Nat) (c : Code) {s : State} {cfg : Computation.GenShiftCtrlCfg State PUnit}
    (h : simRelCtrl n c s cfg) :
    ((sys n c).halts s ↔ (Computation.ControlledEmbed.sys (M := sys n c)).halts cfg) := by
  simpa [simRelCtrl] using (Computation.ControlledEmbed.sim_halts (M := sys n c) h)

end HaltSysBridge

end Discrete
end MirandaDynamics
end HeytingLean
