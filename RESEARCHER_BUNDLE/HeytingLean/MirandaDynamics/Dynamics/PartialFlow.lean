import Mathlib.Algebra.Group.Defs

/-!
# MirandaDynamics.Dynamics: partial flows

For ODEs and manifold integral curves, one typically only gets a **local/partial flow**: the time
evolution map is defined only on some domain. This file defines a minimal “partial flow” abstraction
that is sufficient to induce TKFT-style reaching relations without introducing axioms.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Dynamics

universe u v

/-- A partial flow of an additive monoid `τ` on a type `α`.

This is deliberately minimal: it only records a domain predicate and the `0`/`+` laws with explicit
domain side-conditions. -/
structure PartialFlow (τ : Type u) (α : Type v) [AddMonoid τ] : Type (max u v + 1) where
  /-- Domain predicate: `dom t x` means the time-`t` evolution from `x` is defined. -/
  dom : τ → α → Prop
  /-- The time-`t` evolution map.

  This is total, but is only semantically meaningful when `dom t x` holds. This design keeps the
  API proof-friendly by avoiding dependent `map` arguments. -/
  map : τ → α → α
  /-- The flow is defined at time `0`. -/
  dom_zero : ∀ x : α, dom 0 x
  /-- Time `0` acts as the identity. -/
  map_zero : ∀ x : α, map 0 x = x
  /-- Domain closure for time addition. -/
  dom_add : ∀ (t₁ t₂ : τ) (x : α), dom t₂ x → dom t₁ (map t₂ x) → dom (t₁ + t₂) x
  /-- Time addition law (valid when both sides are defined). -/
  map_add : ∀ (t₁ t₂ : τ) (x : α), dom t₂ x → dom t₁ (map t₂ x) → map (t₁ + t₂) x = map t₁ (map t₂ x)

end Dynamics
end MirandaDynamics
end HeytingLean
