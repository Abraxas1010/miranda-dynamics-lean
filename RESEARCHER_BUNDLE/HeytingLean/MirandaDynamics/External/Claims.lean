import HeytingLean.MirandaDynamics.External.Interfaces

/-!
# MirandaDynamics.External: named “literature claim” wrappers (no axioms)

The Miranda/TKFT/billiards/fluids papers provide deep constructions that are not yet re-proved in
Lean in this repository. To keep downstream code readable, we provide *named wrappers* around the
generic interfaces from `External/Interfaces.lean`.

These structures carry **no axioms**: they are just data packages. Theorems can be stated as

`∀ h : EulerTuringCompleteClaim …, …`

to make the dependence on external mathematics explicit.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace External

universe u

/-! ## TKFT universality (reaching semantics) -/

/-- A named wrapper for TKFT-style universality evidence, at the “reaching relation” level. -/
structure TKFTUniversalityClaim (α : Type u) (β : Type u) : Type (u + 1) where
  tkft : TKFTReachingFunctional α β

/-! ## Billiards computation (periodicity / reachability predicates) -/

/-- A named wrapper for “billiards can compute” used only through an undecidability reduction. -/
structure BilliardsComputesClaim (β : Type u) [Primcodable β] (n : ℕ) (Periodic : β → Prop) : Type (u + 1) where
  haltingToPeriodic : HaltingToPredicate (β := β) n Periodic

/-! ## Euler / Navier–Stokes computation (steady-state predicates) -/

/-- A named wrapper for “Euler steady flows are Turing complete”, used only via reductions. -/
structure EulerTuringCompleteClaim (β : Type u) [Primcodable β] (n : ℕ) (Predicate : β → Prop) : Type (u + 1) where
  haltingToPredicate : HaltingToPredicate (β := β) n Predicate

/-- A named wrapper for “Navier–Stokes steady states are Turing complete”, used only via reductions. -/
structure NavierStokesTuringCompleteClaim (β : Type u) [Primcodable β] (n : ℕ) (Predicate : β → Prop) :
    Type (u + 1) where
  haltingToPredicate : HaltingToPredicate (β := β) n Predicate

end External
end MirandaDynamics
end HeytingLean

