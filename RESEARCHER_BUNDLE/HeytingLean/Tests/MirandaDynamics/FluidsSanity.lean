import HeytingLean.MirandaDynamics.Fluids.ContactLinear
import HeytingLean.MirandaDynamics.Fluids.ContactLinearFlow

/-!
# Tests: MirandaDynamics fluids sanity

Small regression tests for the linear contact-data spine.
-/

namespace HeytingLean.Tests.MirandaDynamics.Fluids

open HeytingLean.MirandaDynamics.Fluids

open scoped BigOperators

noncomputable def trivialContactOnReal : ContactLinear (V := ℝ) where
  α := LinearMap.id
  dα := 0
  R := 1
  alpha_R := by simp
  iota_R := by intro w; simp
  nondeg_ker := by
    intro v hv _h
    -- `α` is the identity map on `ℝ`.
    simpa using hv

example (R' : ℝ) (hα : (trivialContactOnReal.α) R' = 1)
    (hι : ∀ w : ℝ, (trivialContactOnReal.dα R') w = 0) :
    R' = trivialContactOnReal.R :=
  (ContactLinear.reeb_unique (C := trivialContactOnReal) (R' := R') hα hι)

example (t x : ℝ) : trivialContactOnReal.reebFlow t x = x + t := by
  simp [trivialContactOnReal]

end HeytingLean.Tests.MirandaDynamics.Fluids
