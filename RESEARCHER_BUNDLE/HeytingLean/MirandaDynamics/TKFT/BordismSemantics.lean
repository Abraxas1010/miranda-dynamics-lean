import Mathlib.CategoryTheory.Category.Basic
import HeytingLean.MirandaDynamics.TKFT.Reaching

/-!
# MirandaDynamics.TKFT: semantics-only bordisms

The TKFT papers describe a “bordism” together with an induced **reaching semantics**.

To iterate quickly without committing to the full smooth/clean bordism definition, this file
introduces a tiny wrapper `BordismSemantics α β` around `ReachingRel α β` and packages these
semantics-only objects as a category. This isolates the *composition laws* (gluing = relation
composition) from any particular geometric model.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace TKFT

open CategoryTheory

universe u v

/-- A semantics-only TKFT bordism from `In` to `Out`, represented by a reaching relation. -/
structure BordismSemantics (In : Type u) (Out : Type v) : Type (max u v) where
  reach : ReachingRel In Out

namespace BordismSemantics

variable {In : Type u} {Mid : Type u} {Out : Type v}

@[ext] theorem ext {B₁ B₂ : BordismSemantics In Out}
    (h : ∀ x y, B₁.reach.rel x y ↔ B₂.reach.rel x y) : B₁ = B₂ := by
  cases B₁ with
  | mk R₁ =>
    cases B₂ with
    | mk R₂ =>
      have : R₁ = R₂ := ReachingRel.ext (by simpa using h)
      cases this
      rfl

/-- Identity semantics-only bordism (`Eq`). -/
def id (In : Type u) : BordismSemantics In In :=
  ⟨ReachingRel.id In⟩

/-- Composition of semantics-only bordisms (relational composition). -/
def comp (B₁ : BordismSemantics In Mid) (B₂ : BordismSemantics Mid Out) : BordismSemantics In Out :=
  ⟨ReachingRel.comp B₁.reach B₂.reach⟩

@[simp] theorem id_reach (In : Type u) : (id In).reach = ReachingRel.id In := rfl
@[simp] theorem comp_reach (B₁ : BordismSemantics In Mid) (B₂ : BordismSemantics Mid Out) :
    (comp B₁ B₂).reach = ReachingRel.comp B₁.reach B₂.reach := rfl

end BordismSemantics

universe u'

/-- A wrapper around a carrier type for the semantics-only category. -/
structure SemObj : Type (u' + 1) where
  carrier : Type u'

instance : CoeSort SemObj (Type u') :=
  ⟨SemObj.carrier⟩

instance : Category SemObj where
  Hom X Y := BordismSemantics X Y
  id X := BordismSemantics.id X
  comp f g := BordismSemantics.comp f g
  id_comp := by
    intro X Y f
    ext a b
    simpa [BordismSemantics.comp, BordismSemantics.id] using
      congrArg (fun R => R.rel a b) (ReachingRel.id_left f.reach)
  comp_id := by
    intro X Y f
    ext a b
    simpa [BordismSemantics.comp, BordismSemantics.id] using
      congrArg (fun R => R.rel a b) (ReachingRel.id_right f.reach)
  assoc := by
    intro W X Y Z f g h
    ext a d
    simpa [BordismSemantics.comp] using
      congrArg (fun R => R.rel a d) (ReachingRel.assoc f.reach g.reach h.reach)

end TKFT
end MirandaDynamics
end HeytingLean
