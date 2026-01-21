import Mathlib.Data.Set.Lattice

/-!
# MirandaDynamics.Seismic: observation-window kernel

The seismic integration is intended to be *observation-first*: we observe only a finite window of a
signal.

On the semantic side, this is naturally modeled as a **kernel/interior operator** on predicates:

> `K_n S` holds at a state `x` iff **all** states observationally indistinguishable from `x`
> (under an `n`-sample window) lie in `S`.

This operator is:
- monotone,
- meet-preserving,
- idempotent,
- contractive (`K x ≤ x`).

This standalone repo does not depend on HeytingLean's broader `ClosingTheLoop` semantics layer, so
we package the laws locally.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Seismic

open Set

universe u

section

variable {α : Type u}

/-- A contractive, meet-preserving, idempotent endomorphism (an “interior/kernel” operator). -/
structure Kernel {β : Type u} [SemilatticeInf β] where
  toFun : β → β
  monotone' : Monotone toFun
  map_inf' : ∀ x y : β, toFun (x ⊓ y) = toFun x ⊓ toFun y
  idempotent' : ∀ x : β, toFun (toFun x) = toFun x
  apply_le' : ∀ x : β, toFun x ≤ x

namespace Kernel

variable {β : Type u} [SemilatticeInf β]

instance : CoeFun (Kernel (β := β)) (fun _ => β → β) where
  coe k := k.toFun

@[simp] lemma toFun_eq_coe (k : Kernel (β := β)) : k.toFun = k := rfl

lemma monotone (k : Kernel (β := β)) : Monotone k := k.monotone'

@[simp] lemma map_inf (k : Kernel (β := β)) (x y : β) : k (x ⊓ y) = k x ⊓ k y :=
  k.map_inf' x y

@[simp] lemma idempotent (k : Kernel (β := β)) (x : β) : k (k x) = k x :=
  k.idempotent' x

lemma apply_le (k : Kernel (β := β)) (x : β) : k x ≤ x :=
  k.apply_le' x

end Kernel

/-- The `n`-sample observation key for an array.

If `n` exceeds the array length, `take` returns the whole array.
-/
def obsKey (n : Nat) (x : Array α) : Array α :=
  x.take n

/-- Observational indistinguishability: same `obsKey` at window size `n`. -/
def ObsEq (n : Nat) (x y : Array α) : Prop :=
  obsKey (α := α) n x = obsKey (α := α) n y

/-- The observation kernel `K_n` on sets of arrays.

`x ∈ K_n S` iff every `y` with the same `n`-prefix observation is also in `S`.
-/
def obsKernelSet (n : Nat) (S : Set (Array α)) : Set (Array α) :=
  {x | ∀ y, ObsEq (α := α) n x y → y ∈ S}

theorem obsKernelSet_subset (n : Nat) (S : Set (Array α)) : obsKernelSet (α := α) n S ⊆ S := by
  intro x hx
  exact hx x rfl

theorem obsKernelSet_mono (n : Nat) : Monotone (obsKernelSet (α := α) n) := by
  intro S T hST x hx y hy
  exact hST (hx y hy)

theorem obsKernelSet_inf (n : Nat) (S T : Set (Array α)) :
    obsKernelSet (α := α) n (S ⊓ T) = obsKernelSet (α := α) n S ⊓ obsKernelSet (α := α) n T := by
  ext x
  constructor
  · intro hx
    refine ⟨?_, ?_⟩ <;> intro y hy
    · exact (hx y hy).1
    · exact (hx y hy).2
  · rintro ⟨hxS, hxT⟩
    intro y hy
    exact ⟨hxS y hy, hxT y hy⟩

theorem obsKernelSet_idem (n : Nat) (S : Set (Array α)) :
    obsKernelSet (α := α) n (obsKernelSet (α := α) n S) = obsKernelSet (α := α) n S := by
  ext x
  constructor
  · intro hx
    exact hx x rfl
  · intro hx y hy z hz
    have : ObsEq (α := α) n x z := hy.trans hz
    exact hx z this

/-- Bundle `obsKernelSet` as a `Kernel` on `Set (Array α)`. -/
def obsKernel (n : Nat) : Kernel (β := Set (Array α)) where
  toFun := obsKernelSet (α := α) n
  monotone' := obsKernelSet_mono (α := α) n
  map_inf' := obsKernelSet_inf (α := α) n
  idempotent' := obsKernelSet_idem (α := α) n
  apply_le' := obsKernelSet_subset (α := α) n

end

end Seismic
end MirandaDynamics
end HeytingLean

