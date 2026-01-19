import Mathlib.Dynamics.PeriodicPts.Defs
import HeytingLean.MirandaDynamics.Computation.FlowRealization

/-!
# MirandaDynamics.Computation: periodicity transport for flow realizations (WS5+)

Given a data-only realization `R : RealizesDetSysByFlow M`, we get a canonical “time-`dt` map”

* `stepMap R : X → X := fun x => R.ϕ R.dt x`

and can transport discrete iteration/periodicity statements from `M.step` to `stepMap R` on the
image of the encoding `R.enc`.

This is a mechanizable bridge toward the long-horizon Euler/Beltrami/Reeb realizations: the
analytic part can supply `R`, after which these lemmas provide the (fully formal) symbolic-dynamics
consequences about periodic orbits.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Computation

open scoped Pointwise

universe u v w

namespace RealizesDetSysByFlow

variable {Cfg : Type u} {τ : Type v} {X : Type w}
variable [AddMonoid τ] [TopologicalSpace τ] [ContinuousAdd τ] [TopologicalSpace X]
variable {M : DetSys Cfg} (R : RealizesDetSysByFlow (Cfg := Cfg) (τ := τ) (X := X) M)

/-- The time-`dt` map of the realizing flow. -/
def stepMap : X → X :=
  fun x => R.ϕ R.dt x

theorem stepMap_enc (c : Cfg) : (R.stepMap (M := M)) (R.enc c) = R.enc (M.step c) := by
  -- `step_comm` is oriented as `enc (step c) = ϕ dt (enc c)`, so rewrite the RHS.
  simp [stepMap, R.step_comm]

theorem stepMap_iterate (n : Nat) (x : X) :
    (R.stepMap (M := M))^[n] x = R.ϕ (n • R.dt) x := by
  induction n generalizing x with
  | zero =>
    simp
  | succ n ih =>
    -- `f^[n+1] x = f (f^[n] x)` and `ϕ (dt + n•dt) x = ϕ dt (ϕ (n•dt) x)`.
    have hdt : (n + 1) • R.dt = R.dt + (n • R.dt) := by
      simpa [Nat.add_comm, Nat.succ_eq_add_one, one_nsmul] using (add_nsmul R.dt 1 n)
    have hflow :
        R.ϕ ((n + 1) • R.dt) x = R.ϕ R.dt (R.ϕ (n • R.dt) x) := by
      simpa [hdt] using (Flow.map_add (ϕ := R.ϕ) R.dt (n • R.dt) x)
    simp [Function.iterate_succ_apply', stepMap, ih, hflow]

theorem enc_iterate_step (n : Nat) (c : Cfg) :
    R.enc (M.step^[n] c) = (R.stepMap (M := M))^[n] (R.enc c) := by
  -- Compare both sides against the flow-time normal form.
  simp [R.stepMap_iterate (M := M) (n := n), R.iterate_enc (M := M) (n := n)]

theorem isPeriodicPt_enc_of_isPeriodicPt (p : Nat) {c : Cfg} (hc : Function.IsPeriodicPt M.step p c) :
    Function.IsPeriodicPt (R.stepMap (M := M)) p (R.enc c) := by
  -- Expand periodicity for the discrete step and push it through `enc_iterate_step`.
  have hc' : M.step^[p] c = c := by
    simpa [Function.IsPeriodicPt, Function.IsFixedPt] using hc
  have henc : R.enc (M.step^[p] c) = R.enc c := congrArg R.enc hc'
  have : (R.stepMap (M := M))^[p] (R.enc c) = R.enc c := by
    simpa [R.enc_iterate_step (M := M) (n := p)] using henc
  simpa [Function.IsPeriodicPt, Function.IsFixedPt] using this

end RealizesDetSysByFlow

end Computation
end MirandaDynamics
end HeytingLean
