import HeytingLean.MirandaDynamics.TKFT.Reaching
import HeytingLean.MirandaDynamics.Undecidability.Transfers

/-!
# MirandaDynamics: external-results interfaces (no axioms)

The Miranda/TKFT/billiards/fluids papers supply deep geometric and analytic constructions.
Re-proving those constructions in Lean is a major project.

To keep the formalization honest *and* usable, we package the boundary to external results as
explicit Lean **structures** (not axioms). Downstream theorems can then be stated as:

> `∀ h : ExternalConstruction …, …`

so that:
- Lean checks the logic downstream of the construction,
- the construction itself is clearly marked as “external data”,
- there is no hidden `axiom` or proof-gap dependency.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace External

open TKFT
open Undecidability

universe u v

/-! ## TKFT-style reaching functions (as relations, with a principled upgrade to `Part`) -/

/-- A TKFT-style reaching relation (no functionality/uniqueness assumed). -/
structure TKFTReaching (α : Type u) (β : Type v) : Type (max u v) where
  reach : TKFT.ReachingRel α β

/-- A TKFT-style reaching relation with a uniqueness hypothesis, allowing a principled upgrade
to a chosen partial function (`Part`). -/
structure TKFTReachingFunctional (α : Type u) (β : Type v) : Type (max u v) extends TKFTReaching α β where
  functional : TKFT.ReachingRel.Functional reach

/-- Coercion to the underlying reaching relation bundle (for convenient reuse). -/
instance {α : Type u} {β : Type v} : Coe (TKFTReachingFunctional α β) (TKFTReaching α β) :=
  ⟨fun h => h.toTKFTReaching⟩

/-- Backward-compatible name: a “TKFT construction” is a functional reaching relation. -/
abbrev TKFTConstruction (α : Type u) (β : Type v) : Type (max u v) :=
  TKFTReachingFunctional α β

/-- Constructive “inverse-on-image” view that does not require choice. -/
def reachingImage {α : Type u} {β : Type v} (h : TKFTReaching α β) (a : α) : Type v :=
  TKFT.ReachingRel.Image h.reach a

/-- The associated reaching function, obtained by choice from the reaching relation. -/
noncomputable def reachingFunction {α : Type u} {β : Type v} (h : TKFTConstruction α β) :
    α → Part β :=
  TKFT.ReachingRel.toPart (R := h.reach) h.functional

theorem reachingFunction_spec {α : Type u} {β : Type v} (h : TKFTConstruction α β) (a : α) (b : β) :
    b ∈ reachingFunction h a ↔ h.reach.rel a b :=
  TKFT.ReachingRel.toPart_spec (R := h.reach) h.functional a b

/-! ## Undecidability transfer boundary (halting → physical predicate) -/

/-- Package the sole ingredient needed for the undecidability-transfer step:
a computable many-one reduction from halting to some predicate `P`. -/
structure HaltingToPredicate {β : Type v} [Primcodable β] (n : ℕ) (P : β → Prop) : Type (max v 1) where
  red : Undecidability.ManyOne (p := Undecidability.Halting.Halts n) (q := P)

/-- Backward-compatible name. -/
abbrev HaltingReduction {β : Type v} [Primcodable β] (n : ℕ) (P : β → Prop) : Type (max v 1) :=
  HaltingToPredicate (β := β) n P

theorem not_computable_of_haltingReduction {β : Type v} [Primcodable β] {P : β → Prop} (n : ℕ)
    (h : HaltingToPredicate (β := β) n P) : ¬ComputablePred P :=
  Undecidability.Halting.not_computable_of_halting_reduces (n := n) h.red

end External
end MirandaDynamics
end HeytingLean
