import HeytingLean.MirandaDynamics.Computation.GeneralizedShift

/-!
# MirandaDynamics.Computation: periodic-orbit transport for the generalized-shift embedding (WS5+)

This file strengthens `Computation.GeneralizedShift.Embed` with iterate lemmas:

* iterating the generalized-shift step on an embedded configuration agrees with embedding the
  iterated original configuration.

These lemmas are used to transport dynamical predicates (like “reaches a period-2 orbit”) from a
discrete halting model into the generalized shift layer.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Computation

namespace Embed

universe u

variable {Cfg : Type u} (M : HaltSys Cfg)

theorem iterate_step_embedCfg (n : Nat) (c : Cfg) :
    (GenShiftRule.step (rule M))^[n] (embedCfg c) = embedCfg ((M.step)^[n] c) := by
  induction n generalizing c with
  | zero =>
    rfl
  | succ n ih =>
    -- `f^[n+1] x = f (f^[n] x)`; then use the 1-step commutation lemma.
    simp [Function.iterate_succ_apply', ih, step_embedCfg (M := M)]

end Embed

end Computation
end MirandaDynamics
end HeytingLean

