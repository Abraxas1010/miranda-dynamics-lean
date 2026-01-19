import Mathlib.Data.Set.Lattice

/-!
# MirandaDynamics: reachability core (standalone)

Miranda/TKFT-style "dynamical computation" is expressed through a
reachability relation on states.

This standalone version provides:
- `ReachSystem`: a state space with reflexive/transitive reachability
- `K`: safety kernel operator (future-closed predicates)
- `IsInvariant`: invariant predicates under reachability
- `Simulation`: reachability-preserving relations
- `Realizable`: existence-based realizability

This file intentionally contains *no axioms* and *no proof gaps*.

## References

Based on the formalization from HeytingLean's ClosingTheLoop semantics,
adapted for standalone use in the Miranda Dynamics PaperPack.
-/

namespace HeytingLean
namespace MirandaDynamics

open Set

universe u v

/-- A reachability-based computation model: a state space equipped with a reflexive/transitive
reachability relation (think: multi-step reduction, time evolution, etc.). -/
structure ReachSystem where
  State : Type u
  Reach : State → State → Prop
  refl : ∀ x, Reach x x
  trans : ∀ {x y z}, Reach x y → Reach y z → Reach x z

namespace ReachSystem

variable (S : ReachSystem)

/-- Safety kernel induced by reachability: keep states whose every reachable future state lies in `P`. -/
def K (P : Set S.State) : Set S.State :=
  {x | ∀ y, S.Reach x y → y ∈ P}

lemma K_contract (P : Set S.State) : S.K P ⊆ P := by
  intro x hx
  simpa using hx x (S.refl x)

lemma K_monotone : Monotone S.K := by
  intro P Q hPQ x hx y hy
  exact hPQ (hx y hy)

lemma K_idem (P : Set S.State) : S.K (S.K P) = S.K P := by
  ext x
  constructor
  · intro hx y hy
    have hyK : y ∈ S.K P := hx y hy
    exact hyK y (S.refl y)
  · intro hx y hy z hz
    exact hx z (S.trans hy hz)

lemma K_meet (P Q : Set S.State) : S.K (P ∩ Q) = S.K P ∩ S.K Q := by
  ext x
  constructor
  · intro hx
    refine And.intro ?_ ?_
    · intro y hy; exact (hx y hy).1
    · intro y hy; exact (hx y hy).2
  · rintro ⟨hxP, hxQ⟩ y hy
    exact And.intro (hxP y hy) (hxQ y hy)

/-- A predicate is future-closed if it is closed under reachability. -/
def IsInvariant (P : Set S.State) : Prop :=
  ∀ ⦃x y⦄, S.Reach x y → x ∈ P → y ∈ P

lemma K_eq_of_invariant (P : Set S.State) (hInv : S.IsInvariant P) : S.K P = P := by
  ext x
  constructor
  · intro hx; exact S.K_contract P hx
  · intro hx y hy
    exact hInv hy hx

end ReachSystem

/-! ## Relational realizability -/

namespace Realizability

variable {S₁ : ReachSystem} {S₂ : ReachSystem}

/-- A reachability simulation: every reachable future in `S₁` can be matched by a reachable
future in `S₂`, preserving the relation. -/
structure Simulation (R : S₁.State → S₂.State → Prop) : Prop where
  sim : ∀ {x x' y}, R x y → S₁.Reach x x' → ∃ y', S₂.Reach y y' ∧ R x' y'

/-- Existence-based realizability: `x` is realized by some `y ∈ Q` related to it. -/
def Realizable (R : S₁.State → S₂.State → Prop) (Q : Set S₂.State) : Set S₁.State :=
  {x | ∃ y, R x y ∧ y ∈ Q}

/-- If `Q` is invariant in the target system, then the realizable states form an invariant
predicate in the source system. -/
theorem realizable_invariant_of_simulation
    {R : S₁.State → S₂.State → Prop} (hSim : Simulation (S₁ := S₁) (S₂ := S₂) R)
    {Q : Set S₂.State} (hInv : S₂.IsInvariant Q) :
    S₁.IsInvariant (Realizable (S₁ := S₁) (S₂ := S₂) R Q) := by
  intro x x' hx ⟨y, hRxy, hyQ⟩
  rcases hSim.sim hRxy hx with ⟨y', hyReach, hRx'y'⟩
  refine ⟨y', hRx'y', ?_⟩
  exact hInv hyReach hyQ

end Realizability

end MirandaDynamics
end HeytingLean
