import HeytingLean.MirandaDynamics.Fluids.VectorCalculus.GradDiv3

/-!
# Tests: MirandaDynamics grad/div sanity

Compile-time smoke tests for Euclidean `grad`, `div`, and the steady Euler shell.
-/

namespace HeytingLean.Tests.MirandaDynamics.GradDiv

open HeytingLean.MirandaDynamics.Fluids.VectorCalculus
open HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3

example (c : V) : IsEulerSteadyBernoulli (u := fun _ => c) (p := fun _ => (0 : ℝ)) :=
  eulerSteadyBernoulli_const (c := c)

example (u : V → V) (lam : ℝ) (h : IsBeltrami u lam) :
    IsEulerSteadyBernoulli (u := u) (p := fun _ => (0 : ℝ)) :=
  eulerSteadyBernoulli_const_of_beltrami (u := u) (lam := lam) h

end HeytingLean.Tests.MirandaDynamics.GradDiv
