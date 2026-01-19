import Mathlib.Analysis.Convex.Basic
import HeytingLean.MirandaDynamics.Billiards.Geometry

/-!
# MirandaDynamics.Billiards: the unit-square table (staged, proof-grade sets)

This file instantiates the staged billiards `Table` model on the **unit square** in `ℝ²`.

At this stage we only provide:
- the closed table region as a convex `Set` in `EuclideanSpace ℝ (Fin 2)`,
- a boundary predicate (union of the four walls),
- a chosen normal field on the boundary (corners choose an arbitrary normal).

This is a stepping stone toward a deterministic “billiard map” for polygonal tables (WS7.3+).
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open scoped RealInnerProductSpace

namespace UnitSquare

abbrev x (p : V) : ℝ := p 0
abbrev y (p : V) : ℝ := p 1

/-- The closed unit square `[0,1]×[0,1]` as a subset of `ℝ²`. -/
def region : Set V :=
  (Set.univ : Set (Fin 2)).pi fun _ => Set.Icc (0 : ℝ) 1

theorem mem_region_iff (p : V) :
    p ∈ region ↔ (0 ≤ x p ∧ x p ≤ 1) ∧ (0 ≤ y p ∧ y p ≤ 1) := by
  unfold region
  have hpi :
      p ∈ (Set.univ : Set (Fin 2)).pi (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) ↔
        ∀ i : Fin 2, p i ∈ Set.Icc (0 : ℝ) 1 := by
    simpa using
      (Set.mem_univ_pi (f := p) (t := fun _ : Fin 2 => Set.Icc (0 : ℝ) 1))
  constructor
  · intro hp
    have hp' := hpi.mp hp
    have hx' : 0 ≤ x p ∧ x p ≤ 1 := by
      simpa [x] using (hp' 0)
    have hy' : 0 ≤ y p ∧ y p ≤ 1 := by
      simpa [y] using (hp' 1)
    exact ⟨hx', hy'⟩
  · rintro ⟨hx', hy'⟩
    refine hpi.mpr ?_
    intro i
    cases i using Fin.cases with
    | zero =>
      simpa [x] using hx'
    | succ j =>
      cases j using Fin.cases with
      | zero =>
        simpa [y] using hy'
      | succ k =>
        exact (Fin.elim0 k)

/-- The boundary (four walls) of the closed unit square. -/
def boundary : Set V :=
  {p | p ∈ region ∧ (x p = 0 ∨ x p = 1 ∨ y p = 0 ∨ y p = 1)}

theorem boundary_subset_region : boundary ⊆ region := by
  intro p hp
  exact hp.1

/-- The unit square region is convex. -/
theorem convex_region : Convex ℝ region := by
  -- `Set.pi` of convex sets is convex.
  refine convex_pi (𝕜 := ℝ) (s := (Set.univ : Set (Fin 2))) (t := fun _ => Set.Icc (0 : ℝ) 1) ?_
  intro i _hi
  simpa using (convex_Icc (𝕜 := ℝ) (r := (0 : ℝ)) (s := (1 : ℝ)))

theorem segment_subset_region {p q : V} (hp : p ∈ region) (hq : q ∈ region) :
    segment ℝ p q ⊆ region := by
  simpa using (convex_region.segment_subset hp hq)

/-- Standard basis vector `e₀` in `ℝ²`. -/
def eX : V := fun i => if i = 0 then 1 else 0

/-- Standard basis vector `e₁` in `ℝ²`. -/
def eY : V := fun i => if i = 1 then 1 else 0

@[simp] theorem eX_x : x eX = 1 := by simp [eX, x]
@[simp] theorem eX_y : y eX = 0 := by simp [eX, y]
@[simp] theorem eY_x : x eY = 0 := by simp [eY, x]
@[simp] theorem eY_y : y eY = 1 := by simp [eY, y]

/-- A chosen outward normal on the boundary.

At corners we pick the `x`-normal by convention; this will be refined later when corners are excluded. -/
def normal (p : {p // p ∈ boundary}) : V :=
  if x p.1 = 0 ∨ x p.1 = 1 then eX else eY

/-- The staged unit-square billiard table as a `Table`. -/
def table : Table :=
  { inside := region
    boundary := boundary
    normal := normal }

end UnitSquare

end Billiards
end MirandaDynamics
end HeytingLean
