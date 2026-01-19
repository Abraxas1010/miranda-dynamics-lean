import HeytingLean.MirandaDynamics.Billiards.Geometry

/-!
# MirandaDynamics.Billiards: noncomputable deterministic “next collision” from first-hit uniqueness

The staged semantics in `Billiards.Geometry` are *relational*: `Table.Step` is existential and does
not choose a unique next collision.

This file provides a **noncomputable**, semantics-first deterministic `next?` constructor:

- define what it means for a time `t > 0` to be the *first* boundary hit along the ray from a state,
- assuming **existence + uniqueness** of such a first-hit time, select it by classical choice,
- produce the corresponding next reflected state.

This is intended as the glue layer for WS7.3: once “Good states” are proved to have a unique first
hit (excluding corners/tangencies), the global billiard map becomes a definable partial function.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set
open scoped RealInnerProductSpace

namespace Table

variable (T : Table)

namespace DeterministicNext

/-- The boundary point reached at time `t` starting from `s` (ray parameterization). -/
def hitPoint (s : State) (t : ℝ) : V :=
  s.pos + t • s.vel

/-- A time `t` is a valid boundary hit along `s` if the segment stays in `inside ∪ boundary`
and the endpoint lies on the boundary. -/
def IsHitTime (s : State) (t : ℝ) : Prop :=
  0 < t ∧
    let q := hitPoint s t
    q ∈ T.boundary ∧ segment ℝ s.pos q ⊆ T.inside ∪ T.boundary

/-- A hit time is a *first* hit time if there are no earlier boundary hits along the ray. -/
def IsFirstHitTime (s : State) (t : ℝ) : Prop :=
  IsHitTime T s t ∧
    ∀ t' : ℝ, 0 < t' → t' < t → hitPoint s t' ∉ T.boundary

/-- “Good” states for deterministic evolution: there exists a unique first-hit time. -/
def Good (s : State) : Prop :=
  ∃! t : ℝ, IsFirstHitTime T s t

/-- Noncomputable deterministic next collision state, defined on `Good` states. -/
noncomputable def next? (s : State) : Option State :=
  if h : Good T s then
    let t : ℝ := Classical.choose (ExistsUnique.exists h)
    have ht : IsFirstHitTime T s t := (Classical.choose_spec (ExistsUnique.exists h)).1
    let q : V := hitPoint s t
    have hq : q ∈ T.boundary := (ht.1.2).1
    some ⟨q, reflect (T.normal ⟨q, hq⟩) s.vel⟩
  else
    none

theorem next?_eq_some_of_Good {s : State} (h : Good T s) :
    ∃ t : ℝ, ∃ q : V,
      next? T s = some ⟨q, reflect (T.normal ⟨q, (by
        -- boundary membership extracted from the `IsFirstHitTime` witness
        have ht : IsFirstHitTime T s (Classical.choose (ExistsUnique.exists h)) :=
          (Classical.choose_spec (ExistsUnique.exists h)).1
        exact (ht.1.2).1)⟩) s.vel⟩ ∧
        IsFirstHitTime T s t ∧ q = hitPoint s t := by
  classical
  -- Unfold `next?` at `h`.
  refine ⟨Classical.choose (ExistsUnique.exists h), hitPoint s (Classical.choose (ExistsUnique.exists h)), ?_, ?_, rfl⟩
  · simp [next?, h, hitPoint]
  · exact (Classical.choose_spec (ExistsUnique.exists h)).1

theorem Step_of_next?_eq_some {s s' : State} (h : next? T s = some s') : T.Step s s' := by
  classical
  unfold next? at h
  split_ifs at h with hgood
  · -- Extract the chosen time and first-hit properties.
    let t : ℝ := Classical.choose (ExistsUnique.exists hgood)
    have htFirst : IsFirstHitTime T s t := (Classical.choose_spec (ExistsUnique.exists hgood)).1
    have ht : 0 < t := htFirst.1.1
    let q : V := hitPoint s t
    have hq : q ∈ T.boundary := (htFirst.1.2).1
    have hseg : segment ℝ s.pos q ⊆ T.inside ∪ T.boundary := (htFirst.1.2).2
    -- Identify `s'` from the definition.
    have hs' : s' = ⟨q, reflect (T.normal ⟨q, hq⟩) s.vel⟩ := by
      simpa [t, q, hitPoint] using (Option.some.inj h)
    subst hs'
    refine ⟨q, hq, ?_, rfl, rfl⟩
    -- Build `Flight` with this `t`.
    refine ⟨t, ht, rfl, hseg⟩
  · cases h

end DeterministicNext

end Table

end Billiards
end MirandaDynamics
end HeytingLean

