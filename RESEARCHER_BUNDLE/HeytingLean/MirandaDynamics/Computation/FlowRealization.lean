import Mathlib.Dynamics.Flow
import HeytingLean.MirandaDynamics.Computation.TuringMachine

/-!
# MirandaDynamics.Computation: realizing a discrete step function as a time-Δ flow map (WS5+ → Euler track)

This file defines a minimal *data-only* interface for “realizing” a deterministic system as the
time-`dt` map of a (continuous) flow:

* a flow `ϕ : Flow τ X`,
* an encoding `enc : Cfg → X`,
* a time-step `dt : τ`,
* a commutation law `enc (step c) = ϕ dt (enc c)`.

No analytic existence theorem is asserted here; this is the interface the long-horizon
Reeb/Beltrami/Euler realizations can target.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Computation

open scoped Pointwise

universe u v w

structure RealizesDetSysByFlow {Cfg : Type u} {τ : Type v} {X : Type w}
    [AddMonoid τ] [TopologicalSpace τ] [ContinuousAdd τ] [TopologicalSpace X] (M : DetSys Cfg) : Type (max u v w) where
  ϕ : Flow τ X
  dt : τ
  enc : Cfg → X
  step_comm : ∀ c : Cfg, enc (M.step c) = ϕ dt (enc c)

namespace RealizesDetSysByFlow

variable {Cfg : Type u} {τ : Type v} {X : Type w}
variable [AddMonoid τ] [TopologicalSpace τ] [ContinuousAdd τ] [TopologicalSpace X]
variable {M : DetSys Cfg} (R : RealizesDetSysByFlow (Cfg := Cfg) (τ := τ) (X := X) M)

theorem iterate_enc (n : Nat) (c : Cfg) :
    R.enc (M.step^[n] c) = R.ϕ (n • R.dt) (R.enc c) := by
  induction n generalizing c with
  | zero =>
    simp
  | succ n ih =>
    -- unfold one iterate on each side, then use the flow law `ϕ (t₁+t₂) x = ϕ t₁ (ϕ t₂ x)`.
    have hdt : (n + 1) • R.dt = R.dt + (n • R.dt) := by
      -- `(1+n)•dt = dt + n•dt` and `1+n = n+1`.
      simpa [Nat.add_comm, Nat.succ_eq_add_one, one_nsmul] using (add_nsmul R.dt 1 n)
    have hflow : R.ϕ ((n + 1) • R.dt) (R.enc c) = R.ϕ R.dt (R.ϕ (n • R.dt) (R.enc c)) := by
      -- `ϕ (dt + n•dt) x = ϕ dt (ϕ (n•dt) x)`, then rewrite `dt + n•dt`.
      simpa [hdt] using (Flow.map_add (ϕ := R.ϕ) R.dt (n • R.dt) (R.enc c))
    calc
      R.enc (M.step^[n + 1] c) = R.enc (M.step (M.step^[n] c)) := by
        simp [Function.iterate_succ_apply']
      _ = R.ϕ R.dt (R.enc (M.step^[n] c)) := by
        simpa using R.step_comm (c := (M.step^[n] c))
      _ = R.ϕ R.dt (R.ϕ (n • R.dt) (R.enc c)) := by
        simp [ih]
      _ = R.ϕ ((n + 1) • R.dt) (R.enc c) := by
        simp [hflow]

end RealizesDetSysByFlow

end Computation
end MirandaDynamics
end HeytingLean
