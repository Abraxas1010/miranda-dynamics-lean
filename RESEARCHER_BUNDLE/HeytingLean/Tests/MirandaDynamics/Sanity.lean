import HeytingLean.MirandaDynamics

/-!
# Tests: MirandaDynamics sanity

These are small “no proof-gap” regression tests for the MirandaDynamics spine:

- reaching relation category laws,
- union-nucleus fixed-point characterization.
-/

namespace HeytingLean.Tests.MirandaDynamics

open HeytingLean.MirandaDynamics

namespace TKFT

open HeytingLean.MirandaDynamics.TKFT

universe u v w z

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type z}

theorem reaching_id_left (R : ReachingRel α β) :
    ReachingRel.comp (ReachingRel.id α) R = R :=
  ReachingRel.id_left R

theorem reaching_id_right (R : ReachingRel α β) :
    ReachingRel.comp R (ReachingRel.id β) = R :=
  ReachingRel.id_right R

theorem reaching_assoc (R : ReachingRel α β) (S : ReachingRel β γ) (T : ReachingRel γ δ) :
    ReachingRel.comp (ReachingRel.comp R S) T = ReachingRel.comp R (ReachingRel.comp S T) :=
  ReachingRel.assoc R S T

end TKFT

namespace TKFTFlow

open HeytingLean.MirandaDynamics.TKFT

-- Smoke check: `reachingRelOfFlow` is a well-typed reaching relation.
universe u

variable {τ : Type u} [AddMonoid τ] [TopologicalSpace τ] [ContinuousAdd τ]
variable {α : Type u} [TopologicalSpace α]

example (ϕ : Flow τ α) (In Out : Set α) :
    ReachingRel {x // x ∈ In} {y // y ∈ Out} :=
  reachingRelOfFlow (ϕ := ϕ) In Out

end TKFTFlow

namespace TKFTRelCat

open HeytingLean.MirandaDynamics.TKFT
open HeytingLean.MirandaDynamics.TKFT.RelCatBridge

-- Smoke check: there is an explicit equivalence to Mathlib’s relation category.
example : (TKFT.Obj.{0} ≌ CategoryTheory.RelCat.{0}) :=
  equivalence

end TKFTRelCat

namespace FixedPoint

open HeytingLean.MirandaDynamics.FixedPoint

theorem union_fixedPoint_iff_superset {α : Type} (U S : Set α) :
    unionNucleus (α := α) U S = S ↔ U ⊆ S :=
  isFixedPoint_unionNucleus_iff (α := α) U S

end FixedPoint

namespace HeytingTuring

open HeytingLean.MirandaDynamics.HeytingTuring

example {α : Type} (U : Set α) : sInf {S : Set α | U ⊆ S} = U :=
  sInf_supersets_eq (α := α) U

example {α : Type} (U : Set α) :
    sInf {S : Set α | HeytingLean.MirandaDynamics.FixedPoint.unionNucleus (α := α) U S = S} = U :=
  sInf_fixedPoints_unionNucleus_eq (α := α) U

end HeytingTuring

namespace External

open HeytingLean.MirandaDynamics.External

universe u

-- This is a type-level sanity check that the named external-claim wrappers compose with the generic
-- reduction interface. (No concrete instances are asserted here.)
example {β : Type u} [Primcodable β] {P : β → Prop} (n : ℕ)
    (h : BilliardsComputesClaim (β := β) n P) : ¬ComputablePred P :=
  not_computable_of_billiardsComputes (β := β) (Periodic := P) n h

end External

end HeytingLean.Tests.MirandaDynamics
