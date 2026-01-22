import Mathlib.Order.Nucleus
import Mathlib.Data.Set.Lattice
import HeytingLean.MirandaDynamics.TKFT.Reaching

/-!
# MirandaDynamics.Wolfram: “gap nucleus” from TKFT reaching data

The WIP note talks about a “Heyting gap” phenomenon, informally “true but unobservable”.

At the *set/predicate* level, one robust way to model “unobservable states” is to force
every predicate to include a fixed set `F` of “unreachable” states. This is an inflationary
`Nucleus` on `Set α`:

  `j(U) = U ∪ F`.

This file provides that nucleus in a TKFT-friendly wrapper: given a TKFT reaching relation
and a chosen base state `s₀`, we define the set of states not reachable from `s₀` and use it
as the “forced-in” set.

This is intentionally lightweight: it does *not* claim that any specific Miranda billiards
construction yields this nucleus, only that the construction exists as a reusable interface.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Wolfram

open Set

universe u

namespace TKFT

open HeytingLean.MirandaDynamics.TKFT

variable {State : Type u}

/-- States not reachable from a basepoint `s₀`, under a TKFT-style reaching relation. -/
def unreachableFrom (R : ReachingRel State State) (s₀ : State) : Set State :=
  {s | ¬ R.rel s₀ s}

/-- Inflationary nucleus: union “unreachable” states into every predicate. -/
def reachabilityNucleus (R : ReachingRel State State) (s₀ : State) : Nucleus (Set State) where
  toFun U := U ∪ unreachableFrom (R := R) s₀
  map_inf' U V := by
    ext s
    constructor
    · intro hs
      rcases hs with hs | hunr
      · exact ⟨Or.inl hs.1, Or.inl hs.2⟩
      · exact ⟨Or.inr hunr, Or.inr hunr⟩
    · rintro ⟨hsU, hsV⟩
      cases hsU with
      | inl hsU =>
          cases hsV with
          | inl hsV => exact Or.inl ⟨hsU, hsV⟩
          | inr hunr => exact Or.inr hunr
      | inr hunr =>
          exact Or.inr hunr
  idempotent' U := by
    intro s hs
    rcases hs with hs | hunr
    · exact hs
    · exact Or.inr hunr
  le_apply' U := by
    intro s hs
    exact Or.inl hs

@[simp] theorem reachabilityNucleus_apply (R : ReachingRel State State) (s₀ : State) (U : Set State) :
    reachabilityNucleus (R := R) s₀ U = U ∪ unreachableFrom (R := R) s₀ :=
  rfl

end TKFT

end Wolfram
end MirandaDynamics
end HeytingLean

