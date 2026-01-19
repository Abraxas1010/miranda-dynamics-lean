import Mathlib.Analysis.Convex.Segment
import Mathlib.Logic.Relation
import HeytingLean.MirandaDynamics.Billiards.SpecularReflection
import HeytingLean.MirandaDynamics.TKFT.Reaching

/-!
# MirandaDynamics.Billiards: geometry skeleton (tables + trajectory semantics)

This file provides a **staged**, semantics-first foundation for billiard dynamics (WS7):

- a billiard table described by an `inside` region and a `boundary` set;
- a boundary normal field (no regularity assumptions yet);
- a one-step **collision semantics**: straight flight inside the table to a boundary point,
  followed by specular reflection of velocity using `Billiards.reflect`;
- a reachability predicate as reflexive-transitive closure of the step relation.

This is intentionally *not* yet a full “billiard map” (no uniqueness/minimal-time next collision),
but it is already strong enough to express and test the reflection-law invariants and to later
connect billiard reachability to the TKFT `ReachingRel` vocabulary.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open scoped RealInnerProductSpace

/-- A staged billiard table model in `ℝ²`. -/
structure Table where
  /-- Interior points. (No topological assumptions are imposed at this stage.) -/
  inside : Set V
  /-- Boundary points where specular reflection applies. -/
  boundary : Set V
  /-- A chosen boundary normal vector (not assumed unit). -/
  normal : {x // x ∈ boundary} → V

/-- State of a (unit-speed or general-speed) billiard particle: position and velocity. -/
structure State where
  pos : V
  vel : V

namespace Table

variable (T : Table)

/-- Straight-line flight from `p` to `q` with direction `v`, staying in `inside ∪ boundary`. -/
def Flight (p q : V) (v : V) : Prop :=
  ∃ t : ℝ, 0 < t ∧ q = p + t • v ∧ segment ℝ p q ⊆ T.inside ∪ T.boundary

/-- One billiard step: fly to some boundary point, then reflect the velocity at that point. -/
def Step (s s' : State) : Prop :=
  ∃ q : V, ∃ hq : q ∈ T.boundary,
    T.Flight s.pos q s.vel ∧ s'.pos = q ∧ s'.vel = reflect (T.normal ⟨q, hq⟩) s.vel

/-- Billiard reachability: reflexive-transitive closure of `Step`. -/
def Reaches : State → State → Prop :=
  Relation.ReflTransGen T.Step

/-- View reachability as a TKFT-style reaching relation on the state space. -/
def reachingRel : TKFT.ReachingRel State State :=
  ⟨T.Reaches⟩

end Table

namespace Table

variable {T : Table} {s s' : State}

theorem Step.norm_vel_eq (h : T.Step s s') : ‖s'.vel‖ = ‖s.vel‖ := by
  rcases h with ⟨q, hq, _hFlight, _hpos, hvel⟩
  -- `reflect` is a linear isometry equivalence, so it preserves norm.
  rw [hvel]
  exact norm_reflect (n := T.normal ⟨q, hq⟩) (v := s.vel)

@[simp] theorem Reaches.refl (T : Table) (s : State) : T.Reaches s s :=
  Relation.ReflTransGen.refl

theorem Reaches.trans (T : Table) {s₁ s₂ s₃ : State} :
    T.Reaches s₁ s₂ → T.Reaches s₂ s₃ → T.Reaches s₁ s₃ :=
  Relation.ReflTransGen.trans

theorem Step.reaches (h : T.Step s s') : T.Reaches s s' :=
  Relation.ReflTransGen.single h

end Table

end Billiards
end MirandaDynamics
end HeytingLean
