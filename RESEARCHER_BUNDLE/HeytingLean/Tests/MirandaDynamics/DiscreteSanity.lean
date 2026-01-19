import HeytingLean.MirandaDynamics.Discrete.HaltingToPeriodic
import HeytingLean.MirandaDynamics.Discrete.HaltSys

/-!
# Tests: MirandaDynamics discrete sanity

These are small regression tests for the discrete halting ↔ periodic-orbit bridge.
-/

namespace HeytingLean.Tests.MirandaDynamics.Discrete

open HeytingLean.MirandaDynamics.Discrete

open Nat.Partrec
open Nat.Partrec.Code

theorem halts_const0 (n : Nat) : HeytingLean.MirandaDynamics.Undecidability.Halting.Halts n (Code.const 0) := by
  -- `Code.const 0` is definitionally `Code.zero`; for `k := n+1`, the guard `n ≤ k-1` holds.
  unfold HeytingLean.MirandaDynamics.Undecidability.Halting.Halts
  -- Provide a concrete `evaln` witness, then use `halts_iff_exists_evaln`.
  refine (halts_iff_exists_evaln n (Code.const 0)).2 ?_
  refine ⟨n + 1, 0, ?_⟩
  -- unfold `evaln` for `zero`
  -- `evaln (n+1) zero n = some 0` because `n ≤ n`.
  simp [Nat.Partrec.Code.evaln, Nat.Partrec.Code.const]

theorem reachesPeriod2_const0 (n : Nat) :
    ReachesPeriod2 n (Code.const 0) := by
  exact reachesPeriod2_of_halting n (Code.const 0) (halts_const0 n)

theorem haltsFrom_start_const0 (n : Nat) :
    (HaltSysBridge.sys n (Code.const 0)).haltsFrom start := by
  have : HeytingLean.MirandaDynamics.Undecidability.Halting.Halts n (Code.const 0) :=
    halts_const0 n
  exact (HaltSysBridge.haltsFrom_start_iff_halting n (Code.const 0)).2 this

example (n : Nat) (c : Code) :
    HaltSysBridge.simRel n c start (HeytingLean.MirandaDynamics.Computation.Embed.embedCfg (Cfg := State) start) := by
  rfl

example (n : Nat) (c : Code) :
    HaltSysBridge.simRelCtrl n c start (HeytingLean.MirandaDynamics.Computation.ControlledEmbed.embedCfg (Cfg := State) start) := by
  rfl

end HeytingLean.Tests.MirandaDynamics.Discrete
