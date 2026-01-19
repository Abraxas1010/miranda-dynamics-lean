import HeytingLean.MirandaDynamics.Billiards.Geometry
import HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor

/-!
# MirandaDynamics.Billiards: staged table semantics for the two-parabola shift corridor (WS7.3)

`ParabolicShiftCorridor.lean` establishes the affine update on the horizontal coordinate induced by
two parabolic reflections, using explicit reflection formulas.

This file packages the same computation into the staged billiard **step semantics** from
`Geometry.lean`:

* a table whose boundary is a single translated parabola `setWithFocusX a f₀ f`;
* a first step: a vertical downward ray hits the parabola at `pointOn … x0`;
* a second step (in a second table): the reflected ray hits the second parabola at `innerHit … x0`;
* the outgoing velocity after the second reflection is vertical.

This is still *staged*: it does not yet assemble a single global table with a union boundary, nor
does it prove minimal-time uniqueness. It is intended as a mechanizable bridge from the parabola
optics lemmas to WS7.3 “deterministic next-collision” theorems.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set
open scoped RealInnerProductSpace

open Plane
open Parabola

namespace ParabolicShiftCorridor

open HeytingLean.MirandaDynamics.Billiards.Table

/-! ## A staged table whose boundary is one translated parabola -/

noncomputable def parabolaTable (a f₀ f : ℝ) : Billiards.Table :=
  { inside := Set.univ
    boundary := Parabola.setWithFocusX a f₀ f
    normal := fun q => Parabola.normalX a f q.1 }

@[simp] theorem parabolaTable_inside (a f₀ f : ℝ) : (parabolaTable a f₀ f).inside = Set.univ := rfl
@[simp] theorem parabolaTable_boundary (a f₀ f : ℝ) : (parabolaTable a f₀ f).boundary = Parabola.setWithFocusX a f₀ f :=
  rfl

/-! ## First hit: vertical ray to `pointOn` -/

def startPos (a f₀ f₁ x0 : ℝ) : V :=
  Parabola.pointOn a f₀ f₁ x0 + (1 : ℝ) • eY

def startState (a f₀ f₁ x0 : ℝ) : Billiards.State :=
  ⟨startPos a f₀ f₁ x0, -eY⟩

def hitState₁ (a f₀ f₁ x0 : ℝ) : Billiards.State :=
  ⟨Parabola.pointOn a f₀ f₁ x0, reflect (Parabola.normalX a f₁ (Parabola.pointOn a f₀ f₁ x0)) (-eY)⟩

theorem startStep_to_pointOn (a f₀ f₁ x0 : ℝ) :
    (parabolaTable a f₀ f₁).Step (startState a f₀ f₁ x0) (hitState₁ a f₀ f₁ x0) := by
  refine ⟨Parabola.pointOn a f₀ f₁ x0, ?_, ?_, rfl, rfl⟩
  · exact Parabola.pointOn_mem_setWithFocusX a f₀ f₁ x0
  · -- Flight straight down for time `1`.
    refine ⟨(1 : ℝ), by norm_num, ?_, ?_⟩
    · simp [startState, startPos, hitState₁, Parabola.pointOn, smul_add, add_assoc, add_left_comm, add_comm]
    · simp [parabolaTable, Billiards.Table.Flight]

/-! ## Second hit: reflected ray from `pointOn` to `innerHit` -/

def hitState₂ (a f₀ f₁ f₂ x0 : ℝ) : Billiards.State :=
  ⟨Parabola.innerHit a f₀ f₁ f₂ x0,
    reflect (Parabola.normalX a f₂ (Parabola.innerHit a f₀ f₁ f₂ x0))
      (reflect (Parabola.normalX a f₁ (Parabola.pointOn a f₀ f₁ x0)) (-eY))⟩

theorem pointOn_to_innerHit_Flight (a f₀ f₁ f₂ x0 : ℝ) (hf₁ : 0 < f₁)
    (hprog : 0 < (1 - (f₂ / f₁))) :
    ∃ t : ℝ, 0 < t ∧
      Parabola.innerHit a f₀ f₁ f₂ x0 =
        Parabola.pointOn a f₀ f₁ x0 +
          t • reflect (Parabola.normalX a f₁ (Parabola.pointOn a f₀ f₁ x0)) (-eY) := by
  have hf₁ne : f₁ ≠ 0 := ne_of_gt hf₁
  -- Use the explicit “reflects toward the focus” formula to exhibit a time parameter.
  have hp₁ : Parabola.pointOn a f₀ f₁ x0 ∈ Parabola.setWithFocusX a f₀ f₁ :=
    Parabola.pointOn_mem_setWithFocusX a f₀ f₁ x0
  have href :
      reflect (Parabola.normalX a f₁ (Parabola.pointOn a f₀ f₁ x0)) (-eY) =
        ((4 * f₁) / ((x0 - a) ^ 2 + 4 * f₁ ^ 2)) • (Parabola.focusWithX a f₀ - Parabola.pointOn a f₀ f₁ x0) := by
    -- `x (pointOn …) = x0` by definition.
    simpa [Parabola.pointOn, Plane.mk, Plane.x] using
      (Parabola.reflect_neg_eY_eq_smul_focusWithX_sub (a := a) (f₀ := f₀) (f := f₁) hf₁ne hp₁)
  -- Express `innerHit - pointOn` as a scalar multiple of `(focus - pointOn)`.
  have hdiff :
      Parabola.innerHit a f₀ f₁ f₂ x0 - Parabola.pointOn a f₀ f₁ x0 =
        (1 - (f₂ / f₁)) • (Parabola.focusWithX a f₀ - Parabola.pointOn a f₀ f₁ x0) := by
    simp [Parabola.innerHit, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_add, add_smul]
    ring_nf
  -- Choose `t` so that `t • (reflect … (-eY)) = innerHit - pointOn`.
  -- The scalar in `href` is nonzero since `f₁ ≠ 0`.
  have hden : ((x0 - a) ^ 2 + 4 * f₁ ^ 2) ≠ 0 := by
    have hx : 0 ≤ (x0 - a) ^ 2 := by nlinarith
    have hf : 0 < 4 * f₁ ^ 2 := by nlinarith [hf₁ne]
    exact ne_of_gt (lt_of_lt_of_le hf (by nlinarith [hx]))
  have hscale_ne : ((4 * f₁) / ((x0 - a) ^ 2 + 4 * f₁ ^ 2)) ≠ 0 := by
    nlinarith [hf₁ne, hden]
  have hscale_pos : 0 < ((4 * f₁) / ((x0 - a) ^ 2 + 4 * f₁ ^ 2)) := by
    have hnum : 0 < (4 * f₁) := by nlinarith
    have hden' : 0 < ((x0 - a) ^ 2 + 4 * f₁ ^ 2) := by
      have hx : 0 ≤ (x0 - a) ^ 2 := by nlinarith
      have hf : 0 < 4 * f₁ ^ 2 := by nlinarith [hf₁ne]
      exact lt_of_lt_of_le hf (by nlinarith [hx])
    exact div_pos hnum hden'
  let t : ℝ := (1 - (f₂ / f₁)) / ((4 * f₁) / ((x0 - a) ^ 2 + 4 * f₁ ^ 2))
  refine ⟨t, ?_, ?_⟩
  · -- Combine the explicit positivity hypotheses.
    dsimp [t]
    exact div_pos hprog hscale_pos
  · -- Point equation.
    have :
        Parabola.pointOn a f₀ f₁ x0 +
            t • reflect (Parabola.normalX a f₁ (Parabola.pointOn a f₀ f₁ x0)) (-eY) =
          Parabola.pointOn a f₀ f₁ x0 +
            (1 - (f₂ / f₁)) • (Parabola.focusWithX a f₀ - Parabola.pointOn a f₀ f₁ x0) := by
      -- Expand `t` and substitute `href`.
      dsimp [t]
      -- `t • (s • u) = (t*s) • u`.
      simp [href, smul_smul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      ring_nf
    -- Convert to the target `innerHit` using `hdiff`.
    -- Move `pointOn` to the other side.
    have := congrArg (fun q => q - Parabola.pointOn a f₀ f₁ x0) this
    -- Simplify and use `hdiff`.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_add, add_smul, hdiff] using this

theorem pointOn_to_innerHit_Step
    (a f₀ f₁ f₂ x0 : ℝ) (hf₁ : 0 < f₁) (hf₂ : f₂ ≠ 0) (hprog : 0 < (1 - (f₂ / f₁))) :
    (parabolaTable a f₀ f₂).Step (hitState₁ a f₀ f₁ x0) (hitState₂ a f₀ f₁ f₂ x0) := by
  have hf₁ne : f₁ ≠ 0 := ne_of_gt hf₁
  -- Boundary membership of `innerHit`.
  have hmem : Parabola.innerHit a f₀ f₁ f₂ x0 ∈ Parabola.setWithFocusX a f₀ f₂ :=
    Parabola.innerHit_mem_setWithFocusX (a := a) (f₀ := f₀) (f₁ := f₁) (f₂ := f₂) (x0 := x0) hf₁ne hf₂
  refine ⟨Parabola.innerHit a f₀ f₁ f₂ x0, hmem, ?_, rfl, rfl⟩
  -- Flight: use the witness from `pointOn_to_innerHit_Flight`.
  rcases pointOn_to_innerHit_Flight (a := a) (f₀ := f₀) (f₁ := f₁) (f₂ := f₂) (x0 := x0) hf₁ hprog with ⟨t, ht, hq⟩
  refine ⟨t, ht, ?_, ?_⟩
  · -- rewrite the start position/velocity
    simpa [hitState₁, hitState₂] using hq
  · simp [parabolaTable, Billiards.Table.Flight]

theorem reflect_at_innerHit_is_vertical
    (a f₀ f₁ f₂ x0 : ℝ) (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0) :
    ∃ c : ℝ,
      reflect (Parabola.normalX a f₂ (Parabola.innerHit a f₀ f₁ f₂ x0))
          (reflect (Parabola.normalX a f₁ (Parabola.pointOn a f₀ f₁ x0)) (-eY)) =
        c • (-eY) := by
  -- First rewrite the intermediate velocity as a scalar multiple of `(focus - pointOn)`.
  have hp₁ : Parabola.pointOn a f₀ f₁ x0 ∈ Parabola.setWithFocusX a f₀ f₁ :=
    Parabola.pointOn_mem_setWithFocusX a f₀ f₁ x0
  have href :
      reflect (Parabola.normalX a f₁ (Parabola.pointOn a f₀ f₁ x0)) (-eY) =
        ((4 * f₁) / ((x0 - a) ^ 2 + 4 * f₁ ^ 2)) • (Parabola.focusWithX a f₀ - Parabola.pointOn a f₀ f₁ x0) := by
    simpa [Parabola.pointOn, Plane.mk, Plane.x] using
      (Parabola.reflect_neg_eY_eq_smul_focusWithX_sub (a := a) (f₀ := f₀) (f := f₁) hf₁ hp₁)
  -- Show `focus - pointOn` is a scalar multiple of `focus - innerHit`.
  have hdir :
      Parabola.focusWithX a f₀ - Parabola.pointOn a f₀ f₁ x0 =
        (1 - (f₁ / f₂)) • (Parabola.focusWithX a f₀ - Parabola.innerHit a f₀ f₁ f₂ x0) := by
    -- Unfold `innerHit` and compute.
    simp [Parabola.innerHit, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_add, add_smul]
    ring_nf
  -- Apply the “aim at the focus ⇒ vertical” lemma on the second parabola.
  have hp₂ : Parabola.innerHit a f₀ f₁ f₂ x0 ∈ Parabola.setWithFocusX a f₀ f₂ :=
    Parabola.innerHit_mem_setWithFocusX (a := a) (f₀ := f₀) (f₁ := f₁) (f₂ := f₂) (x0 := x0) hf₁ hf₂
  have hvert :
      reflect (Parabola.normalX a f₂ (Parabola.innerHit a f₀ f₁ f₂ x0))
          (Parabola.focusWithX a f₀ - Parabola.innerHit a f₀ f₁ f₂ x0) =
        (((x (Parabola.innerHit a f₀ f₁ f₂ x0) - a) ^ 2 + 4 * f₂ ^ 2) / (4 * f₂)) • (-eY) := by
    -- `x (innerHit) - a` is already the translated coordinate.
    simpa using
      (Parabola.reflect_focusWithX_sub_eq_smul_neg_eY (a := a) (f₀ := f₀) (f := f₂) hf₂ (p := Parabola.innerHit a f₀ f₁ f₂ x0) hp₂)
  -- Combine scalars.
  refine ⟨((4 * f₁) / ((x0 - a) ^ 2 + 4 * f₁ ^ 2)) * (1 - (f₁ / f₂)) *
      (((x (Parabola.innerHit a f₀ f₁ f₂ x0) - a) ^ 2 + 4 * f₂ ^ 2) / (4 * f₂)), ?_⟩
  -- Linearity: pull out scalars and use `hvert`.
  simp [href, hdir, hvert, map_smulₛₗ, LinearIsometryEquiv.map_smul, smul_smul, mul_assoc, mul_left_comm, mul_comm]

end ParabolicShiftCorridor

end Billiards
end MirandaDynamics
end HeytingLean
