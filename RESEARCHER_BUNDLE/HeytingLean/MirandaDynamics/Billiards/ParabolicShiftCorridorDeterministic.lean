import HeytingLean.MirandaDynamics.Billiards.GeometryDeterministicNext
import HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridorTable

/-!
# MirandaDynamics.Billiards: deterministic minimal-time next collision for the two-parabola shift corridor (WS7.3)

This file upgrades the staged two-parabola corridor semantics from
`ParabolicShiftCorridorTable.lean` to *deterministic minimal-time* `Table.DeterministicNext.next?`
statements for the two individual parabola hits.

Scope:
* A first deterministic collision: a vertical downward ray hits the first parabola at time `1`.
* A second deterministic collision (in a second table): the reflected ray hits the second parabola
  at a computable time, with no earlier boundary hits.

This is still corridor-local: it does not assemble a single global table with a union boundary.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set
open scoped RealInnerProductSpace

open Plane

namespace ParabolicShiftCorridor

open Parabola
open Table
open Table.DeterministicNext

/-! ## Parameters for a two-parabola corridor -/

structure Entry where
  a : ℝ
  f₀ : ℝ
  f₁ : ℝ
  f₂ : ℝ
  x0 : ℝ
  hf₁ : 0 < f₁
  hf₂ : 0 < f₂
  hprog : 0 < (1 - (f₂ / f₁))

namespace Entry

theorem hf₁ne (e : Entry) : e.f₁ ≠ 0 := ne_of_gt e.hf₁
theorem hf₂ne (e : Entry) : e.f₂ ≠ 0 := ne_of_gt e.hf₂

end Entry

/-! ## First collision: vertical ray to the first parabola -/

abbrev table₁ (e : Entry) : Billiards.Table :=
  parabolaTable e.a e.f₀ e.f₁

abbrev start₁ (e : Entry) : Billiards.State :=
  startState e.a e.f₀ e.f₁ e.x0

abbrev hit₁ (e : Entry) : Billiards.State :=
  hitState₁ e.a e.f₀ e.f₁ e.x0

private theorem start₁_isFirstHitTime_one (e : Entry) :
    DeterministicNext.IsFirstHitTime (table₁ e) (start₁ e) (1 : ℝ) := by
  classical
  refine ⟨?_, ?_⟩
  · -- `IsHitTime` at `t=1`.
    refine ⟨by norm_num, ?_⟩
    refine ⟨?_, ?_⟩
    · -- Endpoint is `pointOn`, which lies on the boundary parabola.
      have hq :
          DeterministicNext.hitPoint (table₁ e) (start₁ e) 1 = Parabola.pointOn e.a e.f₀ e.f₁ e.x0 := by
        simp [DeterministicNext.hitPoint, table₁, start₁, startState, startPos, Plane.eY]
      simpa [table₁, parabolaTable, hq] using
        (Parabola.pointOn_mem_setWithFocusX e.a e.f₀ e.f₁ e.x0)
    · -- Segment condition is trivial since `inside = univ`.
      simp [table₁, parabolaTable, DeterministicNext.IsHitTime, DeterministicNext.hitPoint, Billiards.Table.Flight]
  · -- No earlier boundary hits for `0 < t < 1`.
    intro t ht0 htlt
    intro hmem
    have hx :
        x (DeterministicNext.hitPoint (table₁ e) (start₁ e) t) = e.x0 := by
      simp [DeterministicNext.hitPoint, table₁, start₁, startState, startPos, Plane.eY, Plane.eX, Plane.x]
    have hy :
        y (DeterministicNext.hitPoint (table₁ e) (start₁ e) t) =
          y (Parabola.pointOn e.a e.f₀ e.f₁ e.x0) + (1 - t) := by
      simp [DeterministicNext.hitPoint, table₁, start₁, startState, startPos, Parabola.pointOn, Plane.eY, Plane.y,
        Plane.mk]
      ring_nf
    have hyOn :
        y (DeterministicNext.hitPoint (table₁ e) (start₁ e) t) =
          (x (DeterministicNext.hitPoint (table₁ e) (start₁ e) t) - e.a) ^ 2 / (4 * e.f₁) + (e.f₀ - e.f₁) := by
      simpa [table₁, parabolaTable, Parabola.setWithFocusX] using hmem
    have hyPoint :
        y (Parabola.pointOn e.a e.f₀ e.f₁ e.x0) =
          (e.x0 - e.a) ^ 2 / (4 * e.f₁) + (e.f₀ - e.f₁) := by
      simp [Parabola.pointOn, Plane.mk, Plane.y]
    have hpos : 0 < 1 - t := sub_pos.2 htlt
    have : y (DeterministicNext.hitPoint (table₁ e) (start₁ e) t) = y (Parabola.pointOn e.a e.f₀ e.f₁ e.x0) := by
      simpa [hx, hyPoint] using hyOn
    nlinarith [hy, this, hpos]

theorem start₁_Good_firstHit (e : Entry) : DeterministicNext.Good (table₁ e) (start₁ e) := by
  classical
  refine ExistsUnique.intro (1 : ℝ) (start₁_isFirstHitTime_one e) ?_
  intro t ht
  by_cases hlt : t < 1
  · have ht0 : 0 < t := ht.1.1
    exact (start₁_isFirstHitTime_one e).2 t ht0 hlt (ht.1.2.1)
  · have hle : 1 ≤ t := le_of_not_gt hlt
    have hhit1 : DeterministicNext.IsHitTime (table₁ e) (start₁ e) (1 : ℝ) :=
      (start₁_isFirstHitTime_one e).1
    have hnot : DeterministicNext.hitPoint (table₁ e) (start₁ e) 1 ∉ (table₁ e).boundary := by
      have ht0 : 0 < (1 : ℝ) := by norm_num
      have hlt' : (1 : ℝ) < t := lt_of_le_of_ne hle (by
        intro hEq
        exact (lt_irrefl (1 : ℝ)) (by simpa [hEq] using hlt))
      exact ht.2 1 ht0 hlt'
    exact (hnot hhit1.2.1).elim

theorem next?_eq_some_hit₁ (e : Entry) :
    DeterministicNext.next? (table₁ e) (start₁ e) = some (hit₁ e) := by
  classical
  have hgood : DeterministicNext.Good (table₁ e) (start₁ e) := start₁_Good_firstHit e
  have ht :
      Classical.choose (ExistsUnique.exists hgood) = (1 : ℝ) :=
    ExistsUnique.unique hgood (Classical.choose_spec (ExistsUnique.exists hgood))
      (start₁_isFirstHitTime_one e)
  have hq : DeterministicNext.hitPoint (table₁ e) (start₁ e) (1 : ℝ) ∈ (table₁ e).boundary :=
    (start₁_isFirstHitTime_one e).1.2.1
  simp [DeterministicNext.next?, hgood, ht, DeterministicNext.hitPoint, table₁, parabolaTable, start₁, startState,
    startPos, hit₁, hitState₁, hq, Plane.eY]

/-! ## Second collision: reflected ray to the second parabola -/

abbrev table₂ (e : Entry) : Billiards.Table :=
  parabolaTable e.a e.f₀ e.f₂

abbrev start₂ (e : Entry) : Billiards.State :=
  hitState₁ e.a e.f₀ e.f₁ e.x0

abbrev hit₂ (e : Entry) : Billiards.State :=
  hitState₂ e.a e.f₀ e.f₁ e.f₂ e.x0

noncomputable def hitTime₂ (e : Entry) : ℝ :=
  (1 - (e.f₂ / e.f₁)) / ((4 * e.f₁) / ((e.x0 - e.a) ^ 2 + 4 * e.f₁ ^ 2))

theorem hitTime₂_pos (e : Entry) : 0 < hitTime₂ e := by
  have hnum : 0 < (1 - (e.f₂ / e.f₁)) := e.hprog
  have hden : 0 < ((4 * e.f₁) / ((e.x0 - e.a) ^ 2 + 4 * e.f₁ ^ 2)) := by
    have hnum' : 0 < 4 * e.f₁ := by nlinarith [e.hf₁]
    have hden' : 0 < (e.x0 - e.a) ^ 2 + 4 * e.f₁ ^ 2 := by
      have hx : 0 ≤ (e.x0 - e.a) ^ 2 := by nlinarith
      have hf : 0 < 4 * e.f₁ ^ 2 := by nlinarith [e.Entry.hf₁ne]
      exact lt_of_lt_of_le hf (by nlinarith [hx])
    exact div_pos hnum' hden'
  exact div_pos hnum hden

private theorem start₂_vel_eq_smul_focus_sub (e : Entry) :
    (start₂ e).vel =
      ((4 * e.f₁) / ((e.x0 - e.a) ^ 2 + 4 * e.f₁ ^ 2)) •
        (Parabola.focusWithX e.a e.f₀ - Parabola.pointOn e.a e.f₀ e.f₁ e.x0) := by
  -- Apply the translated parabola reflection property at `pointOn`.
  have hp₁ : Parabola.pointOn e.a e.f₀ e.f₁ e.x0 ∈ Parabola.setWithFocusX e.a e.f₀ e.f₁ :=
    Parabola.pointOn_mem_setWithFocusX e.a e.f₀ e.f₁ e.x0
  have href :=
    Parabola.reflect_neg_eY_eq_smul_focusWithX_sub (a := e.a) (f₀ := e.f₀) (f := e.f₁) (hf := e.hf₁ne) (p := Parabola.pointOn e.a e.f₀ e.f₁ e.x0) hp₁
  -- Simplify `x(pointOn) - a = x0 - a`.
  simpa [start₂, hitState₁, Parabola.pointOn, Plane.mk, Plane.x] using href

private theorem hitPoint₂_eq_innerHit (e : Entry) :
    DeterministicNext.hitPoint (table₂ e) (start₂ e) (hitTime₂ e) = Parabola.innerHit e.a e.f₀ e.f₁ e.f₂ e.x0 := by
  -- Reparametrize the ray using the focus direction.
  have hv := start₂_vel_eq_smul_focus_sub e
  have hcpos :
      0 < ((4 * e.f₁) / ((e.x0 - e.a) ^ 2 + 4 * e.f₁ ^ 2)) := by
    have hnum' : 0 < 4 * e.f₁ := by nlinarith [e.hf₁]
    have hden' : 0 < (e.x0 - e.a) ^ 2 + 4 * e.f₁ ^ 2 := by
      have hx : 0 ≤ (e.x0 - e.a) ^ 2 := by nlinarith
      have hf : 0 < 4 * e.f₁ ^ 2 := by nlinarith [e.Entry.hf₁ne]
      exact lt_of_lt_of_le hf (by nlinarith [hx])
    exact div_pos hnum' hden'
  have hcne : ((4 * e.f₁) / ((e.x0 - e.a) ^ 2 + 4 * e.f₁ ^ 2)) ≠ 0 := ne_of_gt hcpos
  -- Expand `hitPoint`.
  simp [DeterministicNext.hitPoint, table₂, parabolaTable, start₂, hitState₁] at *
  -- Use `hv` to rewrite the velocity, then choose `t` so that the scalar along `(focus - pointOn)` is `1 - f₂/f₁`.
  have :
      (Parabola.pointOn e.a e.f₀ e.f₁ e.x0 +
          hitTime₂ e • ((4 * e.f₁) / ((e.x0 - e.a) ^ 2 + 4 * e.f₁ ^ 2)) •
            (Parabola.focusWithX e.a e.f₀ - Parabola.pointOn e.a e.f₀ e.f₁ e.x0)) =
        Parabola.pointOn e.a e.f₀ e.f₁ e.x0 +
          (1 - (e.f₂ / e.f₁)) • (Parabola.focusWithX e.a e.f₀ - Parabola.pointOn e.a e.f₀ e.f₁ e.x0) := by
    -- `hitTime₂` is defined so that `hitTime₂ * c = 1 - f₂/f₁`.
    have : hitTime₂ e * ((4 * e.f₁) / ((e.x0 - e.a) ^ 2 + 4 * e.f₁ ^ 2)) = (1 - (e.f₂ / e.f₁)) := by
      -- Multiply both sides of the definition by the positive denominator.
      simp [hitTime₂, hcne, mul_div_cancel_left₀]
      ring_nf
    -- Normalize scalar multiplication.
    simp [smul_smul, this, mul_assoc, mul_left_comm, mul_comm]
  -- Rewrite to `innerHit` using the alternative expression.
  -- `innerHit = pointOn + (1 - f₂/f₁) • (focus - pointOn)`.
  have hinner :
      Parabola.innerHit e.a e.f₀ e.f₁ e.f₂ e.x0 =
        Parabola.pointOn e.a e.f₀ e.f₁ e.x0 +
          (1 - (e.f₂ / e.f₁)) • (Parabola.focusWithX e.a e.f₀ - Parabola.pointOn e.a e.f₀ e.f₁ e.x0) := by
    -- Unfold `innerHit` and rearrange.
    simp [Parabola.innerHit, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_add, add_smul]
    ring_nf
  -- Put everything together.
  -- Start from the definition of `start₂` and substitute `hv`.
  simpa [DeterministicNext.hitPoint, start₂, hitState₁, hv, hinner, table₂, parabolaTable] using this.symm

theorem hitPoint₂_mem_boundary (e : Entry) :
    DeterministicNext.hitPoint (table₂ e) (start₂ e) (hitTime₂ e) ∈ (table₂ e).boundary := by
  -- It is `innerHit`, which lies on the second parabola.
  have hEq : DeterministicNext.hitPoint (table₂ e) (start₂ e) (hitTime₂ e) =
      Parabola.innerHit e.a e.f₀ e.f₁ e.f₂ e.x0 := hitPoint₂_eq_innerHit e
  have hmem : Parabola.innerHit e.a e.f₀ e.f₁ e.f₂ e.x0 ∈ Parabola.setWithFocusX e.a e.f₀ e.f₂ :=
    Parabola.innerHit_mem_setWithFocusX (a := e.a) (f₀ := e.f₀) (f₁ := e.f₁) (f₂ := e.f₂) (x0 := e.x0)
      e.hf₁ne e.hf₂ne
  simpa [table₂, parabolaTable, hEq] using hmem

private theorem start₂_noHit_before_hitTime₂ (e : Entry) {t : ℝ} (ht0 : 0 < t) (htlt : t < hitTime₂ e) :
    DeterministicNext.hitPoint (table₂ e) (start₂ e) t ∉ (table₂ e).boundary := by
  classical
  have hv0 := start₂_vel_eq_smul_focus_sub e
  -- Use the same scalar as in `hv0`.
  set c : ℝ := ((4 * e.f₁) / ((e.x0 - e.a) ^ 2 + 4 * e.f₁ ^ 2))
  have hv : (start₂ e).vel = c • (Parabola.focusWithX e.a e.f₀ - Parabola.pointOn e.a e.f₀ e.f₁ e.x0) := by
    simpa [c] using hv0
  have hcpos : 0 < c := by
    have hnum : 0 < 4 * e.f₁ := by nlinarith [e.hf₁]
    have hden : 0 < (e.x0 - e.a) ^ 2 + 4 * e.f₁ ^ 2 := by
      have hx : 0 ≤ (e.x0 - e.a) ^ 2 := by nlinarith
      have hf : 0 < 4 * e.f₁ ^ 2 := by nlinarith [e.hf₁ne]
      exact lt_of_lt_of_le hf (by nlinarith [hx])
    simpa [c] using div_pos hnum hden
  have hcne : c ≠ 0 := ne_of_gt hcpos
  set u : ℝ := t * c
  set s : ℝ := 1 - u
  have hu_lt : u < (1 - (e.f₂ / e.f₁)) := by
    have hmul : hitTime₂ e * c = (1 - (e.f₂ / e.f₁)) := by
      simp [hitTime₂, c, hcne, mul_div_cancel_left₀]
      ring_nf
    have : t * c < hitTime₂ e * c := mul_lt_mul_of_pos_right htlt hcpos
    simpa [u, hmul] using this
  have hs_pos : 0 < s := by
    have hu1 : u < 1 := lt_of_lt_of_le hu_lt (by nlinarith [e.hf₁, e.hf₂])
    have : 0 < 1 - u := sub_pos.2 hu1
    simpa [s] using this
  intro hmem
  -- Rewrite the hit point along the focus direction.
  have hq :
      DeterministicNext.hitPoint (table₂ e) (start₂ e) t =
        Parabola.pointOn e.a e.f₀ e.f₁ e.x0 +
          u • (Parabola.focusWithX e.a e.f₀ - Parabola.pointOn e.a e.f₀ e.f₁ e.x0) := by
    simp [DeterministicNext.hitPoint, start₂, hitState₁, hv, u, smul_smul, mul_assoc, mul_left_comm, mul_comm,
      add_assoc, add_left_comm, add_comm]
  have hmem' :
      (Parabola.pointOn e.a e.f₀ e.f₁ e.x0 +
            u • (Parabola.focusWithX e.a e.f₀ - Parabola.pointOn e.a e.f₀ e.f₁ e.x0)) ∈
          Parabola.setWithFocusX e.a e.f₀ e.f₂ := by
    simpa [hq, table₂, parabolaTable] using hmem
  -- Parabola equation (subtracting `f₀`).
  have hEqPar :
      y (Parabola.pointOn e.a e.f₀ e.f₁ e.x0 +
              u • (Parabola.focusWithX e.a e.f₀ - Parabola.pointOn e.a e.f₀ e.f₁ e.x0)) - e.f₀ =
        (x (Parabola.pointOn e.a e.f₀ e.f₁ e.x0 +
                u • (Parabola.focusWithX e.a e.f₀ - Parabola.pointOn e.a e.f₀ e.f₁ e.x0)) - e.a) ^ 2 /
            (4 * e.f₂) - e.f₂ := by
    have hyEq :
        y (Parabola.pointOn e.a e.f₀ e.f₁ e.x0 +
                u • (Parabola.focusWithX e.a e.f₀ - Parabola.pointOn e.a e.f₀ e.f₁ e.x0)) =
          (x (Parabola.pointOn e.a e.f₀ e.f₁ e.x0 +
                  u • (Parabola.focusWithX e.a e.f₀ - Parabola.pointOn e.a e.f₀ e.f₁ e.x0)) - e.a) ^ 2 /
              (4 * e.f₂) + (e.f₀ - e.f₂) := by
      simpa [Parabola.setWithFocusX] using hmem'
    nlinarith [hyEq]
  -- Coordinate computations.
  have hx :
      x (Parabola.pointOn e.a e.f₀ e.f₁ e.x0 +
              u • (Parabola.focusWithX e.a e.f₀ - Parabola.pointOn e.a e.f₀ e.f₁ e.x0)) - e.a =
        s * (e.x0 - e.a) := by
    simp [s, Parabola.pointOn, Parabola.focusWithX, Plane.mk, Plane.x, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm, mul_assoc, mul_left_comm, mul_comm]
    ring_nf
  have hy :
      y (Parabola.pointOn e.a e.f₀ e.f₁ e.x0 +
              u • (Parabola.focusWithX e.a e.f₀ - Parabola.pointOn e.a e.f₀ e.f₁ e.x0)) - e.f₀ =
        s * ((e.x0 - e.a) ^ 2 / (4 * e.f₁) - e.f₁) := by
    simp [s, Parabola.pointOn, Parabola.focusWithX, Plane.mk, Plane.y, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm, mul_assoc, mul_left_comm, mul_comm]
    ring_nf
  have hEqS :
      s * ((e.x0 - e.a) ^ 2 / (4 * e.f₁) - e.f₁) =
        (s * (e.x0 - e.a)) ^ 2 / (4 * e.f₂) - e.f₂ := by
    simpa [hx, hy] using hEqPar
  have hf₁ne : e.f₁ ≠ 0 := e.hf₁ne
  have hf₂ne : e.f₂ ≠ 0 := e.hf₂ne
  have h0 := hEqS
  field_simp [hf₁ne, hf₂ne] at h0
  have hPoly :
      (e.f₁ * (e.x0 - e.a) ^ 2) * s ^ 2 +
          (4 * e.f₁ ^ 2 * e.f₂) * s - (e.f₂ * (e.x0 - e.a) ^ 2) * s - 4 * e.f₁ * e.f₂ ^ 2 = 0 := by
    nlinarith [h0]
  have hFactor :
      (e.f₁ * s - e.f₂) * ((e.x0 - e.a) ^ 2 * s + 4 * e.f₁ * e.f₂) = 0 := by
    have hexp :
        (e.f₁ * s - e.f₂) * ((e.x0 - e.a) ^ 2 * s + 4 * e.f₁ * e.f₂) =
          (e.f₁ * (e.x0 - e.a) ^ 2) * s ^ 2 +
            (4 * e.f₁ ^ 2 * e.f₂) * s - (e.f₂ * (e.x0 - e.a) ^ 2) * s - 4 * e.f₁ * e.f₂ ^ 2 := by
      ring_nf
    simpa [hexp] using hPoly
  have hPos2 : 0 < (e.x0 - e.a) ^ 2 * s + 4 * e.f₁ * e.f₂ := by
    have hx0 : 0 ≤ (e.x0 - e.a) ^ 2 := by nlinarith
    have hx0s : 0 ≤ (e.x0 - e.a) ^ 2 * s := mul_nonneg hx0 (le_of_lt hs_pos)
    have hf : 0 < 4 * e.f₁ * e.f₂ := by nlinarith [e.hf₁, e.hf₂]
    nlinarith
  have h1 : e.f₁ * s - e.f₂ = 0 :=
    (mul_eq_zero.mp hFactor).resolve_right (ne_of_gt hPos2)
  have hsEq : s = e.f₂ / e.f₁ := by
    have hf₁pos : 0 < e.f₁ := e.hf₁
    nlinarith [h1, hf₁pos]
  have huEq : u = 1 - (e.f₂ / e.f₁) := by nlinarith [hsEq, s]
  have htEq : t = hitTime₂ e := by
    have : t * c = 1 - (e.f₂ / e.f₁) := by simpa [u, huEq]
    have : t = (1 - (e.f₂ / e.f₁)) / c := by
      field_simp [hcne] at this
      nlinarith
    simpa [hitTime₂, c] using this
  exact (not_lt_of_eq htEq) htlt

theorem start₂_Good_firstHit (e : Entry) : DeterministicNext.Good (table₂ e) (start₂ e) := by
  classical
  refine ExistsUnique.intro (hitTime₂ e) ?exist ?uniq
  · refine And.intro ?hit ?noEarlier
    · refine ⟨hitTime₂_pos e, ?_⟩
      refine ⟨hitPoint₂_mem_boundary e, ?_⟩
      simp [table₂, parabolaTable, DeterministicNext.IsHitTime, DeterministicNext.hitPoint, Billiards.Table.Flight]
    · intro t ht0 htlt
      exact start₂_noHit_before_hitTime₂ e (t := t) ht0 htlt
  · intro t htFirst
    -- Any first-hit time must match `hitTime₂` since it is itself a hit time.
    have hhit : DeterministicNext.IsHitTime (table₂ e) (start₂ e) (hitTime₂ e) := by
      refine ⟨hitTime₂_pos e, ?_⟩
      refine ⟨hitPoint₂_mem_boundary e, ?_⟩
      simp [table₂, parabolaTable, DeterministicNext.IsHitTime, DeterministicNext.hitPoint, Billiards.Table.Flight]
    have ht_le : t ≤ hitTime₂ e := by
      by_contra hgt
      have hlt : hitTime₂ e < t := lt_of_not_ge hgt
      have : DeterministicNext.hitPoint (table₂ e) (start₂ e) (hitTime₂ e) ∉ (table₂ e).boundary :=
        (htFirst.2) (hitTime₂ e) (hitTime₂_pos e) hlt
      exact this (hhit.2.1)
    have ht_ge : hitTime₂ e ≤ t := by
      by_contra hlt
      have htlt : t < hitTime₂ e := lt_of_not_ge hlt
      have htpos : 0 < t := htFirst.1.1
      have : DeterministicNext.hitPoint (table₂ e) (start₂ e) t ∉ (table₂ e).boundary :=
        start₂_noHit_before_hitTime₂ e (t := t) htpos htlt
      exact this (htFirst.1.2.1)
    exact le_antisymm ht_le ht_ge

theorem next?_eq_some_hit₂ (e : Entry) :
    DeterministicNext.next? (table₂ e) (start₂ e) = some (hit₂ e) := by
  classical
  have hgood : DeterministicNext.Good (table₂ e) (start₂ e) := start₂_Good_firstHit e
  have hq : DeterministicNext.hitPoint (table₂ e) (start₂ e) (hitTime₂ e) ∈ (table₂ e).boundary :=
    hitPoint₂_mem_boundary e
  -- Unfold `next?` at the `Good` witness and use the uniqueness of the chosen time.
  simp [DeterministicNext.next?, hgood, DeterministicNext.hitPoint, table₂, parabolaTable, start₂, hitState₁, hit₂,
    hitState₂, hq, hitPoint₂_eq_innerHit]

/-! ## Two-bounce corridor wrapper (still table-local) -/

/-- Two-step deterministic evolution: first hit on parabola `f₁`, then hit on parabola `f₂`. -/
noncomputable def next2? (e : Entry) : Option Billiards.State :=
  (DeterministicNext.next? (table₁ e) (start₁ e)).bind fun s =>
    DeterministicNext.next? (table₂ e) s

theorem next2?_eq_some_hit₂ (e : Entry) : next2? e = some (hit₂ e) := by
  simp [next2?, next?_eq_some_hit₁, next?_eq_some_hit₂, start₂]

theorem hit₂_vel_is_vertical (e : Entry) : ∃ c : ℝ, (hit₂ e).vel = c • (-eY) := by
  simpa [hit₂, hitState₂] using
    (reflect_at_innerHit_is_vertical (a := e.a) (f₀ := e.f₀) (f₁ := e.f₁) (f₂ := e.f₂) (x0 := e.x0)
      (hf₁ := e.hf₁ne) (hf₂ := e.hf₂ne))

/-! ## Semiconjugacy: induced affine update on the horizontal coordinate -/

theorem x_hitPoint₂_eq_affineUpdate (e : Entry) :
    x (DeterministicNext.hitPoint (table₂ e) (start₂ e) (hitTime₂ e)) =
      Parabola.affineUpdate e.a e.f₁ e.f₂ e.x0 := by
  -- The hit point is `innerHit`, and `x(innerHit) = affineUpdate`.
  have hEq := hitPoint₂_eq_innerHit e
  simpa [hEq] using (Parabola.x_innerHit (a := e.a) (f₀ := e.f₀) (f₁ := e.f₁) (f₂ := e.f₂) (x0 := e.x0))

theorem x_hit₂_eq_affineUpdate (e : Entry) : x (hit₂ e).pos = Parabola.affineUpdate e.a e.f₁ e.f₂ e.x0 := by
  simpa [hit₂, hitState₂] using
    (Parabola.x_innerHit (a := e.a) (f₀ := e.f₀) (f₁ := e.f₁) (f₂ := e.f₂) (x0 := e.x0))

end ParabolicShiftCorridor

end Billiards
end MirandaDynamics
end HeytingLean
