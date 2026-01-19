import Mathlib.CategoryTheory.Category.RelCat
import HeytingLean.MirandaDynamics.TKFT.Category

/-!
# MirandaDynamics.TKFT: bridge to Mathlib’s `RelCat`

Mathlib already provides `CategoryTheory.RelCat`, the category of types with relations as morphisms.
Our `TKFT.Obj` category is the same idea, packaged with a local `ReachingRel` type.

This file builds an explicit equivalence:

`HeytingLean.MirandaDynamics.TKFT.Obj  ≌  CategoryTheory.RelCat`

so downstream category-theoretic constructions can reuse Mathlib’s existing infrastructure.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace TKFT

open CategoryTheory

universe u

namespace RelCatBridge

/-- Interpret a `TKFT.Obj` as a `RelCat` object (a type synonym). -/
def toSetRel {X Y : Type u} (R : ReachingRel X Y) : SetRel X Y :=
  { p | R.rel p.1 p.2 }

@[simp] theorem mem_toSetRel {X Y : Type u} (R : ReachingRel X Y) (x : X) (y : Y) :
    (x, y) ∈ toSetRel R ↔ R.rel x y :=
  Iff.rfl

/-- Interpret a `SetRel` as a `ReachingRel`. -/
def ofSetRel {X Y : Type u} (r : SetRel X Y) : ReachingRel X Y :=
  ⟨fun x y => (x, y) ∈ r⟩

@[simp] theorem ofSetRel_rel {X Y : Type u} (r : SetRel X Y) (x : X) (y : Y) :
    (ofSetRel r).rel x y ↔ (x, y) ∈ r :=
  Iff.rfl

def toRelCat : TKFT.Obj.{u} ⥤ CategoryTheory.RelCat.{u} where
  obj X := X.carrier
  map {X Y} R := CategoryTheory.RelCat.Hom.ofRel (toSetRel R)
  map_id := by
    intro X
    rfl
  map_comp := by
    intro X Y Z f g
    rfl

/-- Interpret a `RelCat` object as a `TKFT.Obj`. -/
def fromRelCat : CategoryTheory.RelCat.{u} ⥤ TKFT.Obj.{u} where
  obj X := ⟨X⟩
  map {X Y} r := ofSetRel r.rel
  map_id := by
    intro X
    rfl
  map_comp := by
    intro X Y Z f g
    rfl

@[simp] theorem toRelCat_obj (X : TKFT.Obj.{u}) : toRelCat.obj X = X.carrier := rfl
@[simp] theorem fromRelCat_obj (X : CategoryTheory.RelCat.{u}) : fromRelCat.obj X = ⟨X⟩ := rfl

/-- `TKFT.Obj` is (definitionally) equivalent to `RelCat`. -/
def equivalence : TKFT.Obj.{u} ≌ CategoryTheory.RelCat.{u} where
  functor := toRelCat
  inverse := fromRelCat
  unitIso :=
    NatIso.ofComponents
      (fun X => by
        cases X
        exact Iso.refl _)
      (by
        intro X Y f
        cases X
        cases Y
        -- `toRelCat ⋙ fromRelCat` is identity on objects, and on morphisms it is `ofSetRel (toSetRel _)`.
        -- So naturality reduces to `f = ofSetRel (toSetRel f)`.
        simp [toRelCat, fromRelCat, toSetRel, ofSetRel]
        refine ReachingRel.ext ?_
        intro a b
        rfl)
  counitIso :=
    NatIso.ofComponents
      (fun X => Iso.refl X)
      (by
        intro X Y f
        -- `Iso.refl` components reduce naturality to `((fromRelCat ⋙ toRelCat).map f = f)`.
        simp
        cases f with
        | ofRel r =>
          refine CategoryTheory.RelCat.Hom.ext _ _ ?_
          ext p
          cases p
          rfl)
  functor_unitIso_comp := by
    intro X
    cases X
    simp

end RelCatBridge

end TKFT
end MirandaDynamics
end HeytingLean
