import HeytingLean.MirandaDynamics.Billiards.UnitSquare

/-!
# MirandaDynamics.Billiards: a deterministic (partial) billiard map for the unit square

This file refines the staged collision semantics (`Table.Step`) for the unit square to a **partial,
deterministic** “next collision” map (WS7.3).

Because polygonal billiards are singular at corners, this map is defined only when the next impact
is **not** a corner hit.

We provide:
- a phase space `CollisionState` (boundary point + inward-pointing velocity),
- `next? : CollisionState → Option CollisionState` selecting the next collision,
- reachability as reflexive-transitive closure of `stepRel`,
- a refinement lemma: `stepRel` implies the staged relational step `UnitSquare.table.Step`.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open scoped RealInnerProductSpace

namespace UnitSquareMap

open UnitSquare

abbrev vx (v : V) : ℝ := x v
abbrev vy (v : V) : ℝ := y v

@[simp] lemma x_add_smul (p v : V) (t : ℝ) : x (p + t • v) = x p + t * x v := by
  simp [x]

@[simp] lemma y_add_smul (p v : V) (t : ℝ) : y (p + t • v) = y p + t * y v := by
  simp [y]

def IsCorner (p : V) : Prop :=
  (x p = 0 ∨ x p = 1) ∧ (y p = 0 ∨ y p = 1)

def Inward (p : V) (v : V) : Prop :=
  (x p = 0 → 0 < x v) ∧
  (x p = 1 → x v < 0) ∧
  (y p = 0 → 0 < y v) ∧
  (y p = 1 → y v < 0)

theorem region_of_boundary {p : V} (hp : p ∈ boundary) : p ∈ region :=
  hp.1

theorem x_bounds_of_boundary {p : V} (hp : p ∈ boundary) : 0 ≤ x p ∧ x p ≤ 1 := by
  have : p ∈ region := region_of_boundary hp
  exact (mem_region_iff p).1 this |>.1

theorem y_bounds_of_boundary {p : V} (hp : p ∈ boundary) : 0 ≤ y p ∧ y p ≤ 1 := by
  have : p ∈ region := region_of_boundary hp
  exact (mem_region_iff p).1 this |>.2

def timeToX? (p v : V) : Option ℝ :=
  if 0 < x v then
    some ((1 - x p) / x v)
  else if x v < 0 then
    some ((0 - x p) / x v)
  else
    none

def timeToY? (p v : V) : Option ℝ :=
  if 0 < y v then
    some ((1 - y p) / y v)
  else if y v < 0 then
    some ((0 - y p) / y v)
  else
    none

inductive HitKind where
  | hitX
  | hitY
  deriving DecidableEq

/-- Choose the next wall-hit time and whether the hit is vertical or horizontal.

Returns `none` exactly for degenerate cases (zero velocity or a corner hit). -/
def nextHit? (p v : V) : Option (HitKind × ℝ) :=
  match timeToX? p v, timeToY? p v with
  | none, none => none
  | some tx, none => some (HitKind.hitX, tx)
  | none, some ty => some (HitKind.hitY, ty)
  | some tx, some ty =>
      if tx < ty then some (HitKind.hitX, tx)
      else if ty < tx then some (HitKind.hitY, ty)
      else none

structure CollisionState where
  pos : V
  pos_mem : pos ∈ boundary
  vel : V
  vel_ne_zero : vel ≠ 0

def CollisionState.toState (s : CollisionState) : State :=
  ⟨s.pos, s.vel⟩

/-!
## WS7.3 followup: “good” states where `next?` is provably defined

The staged `next?` definition computes a candidate impact point `q := p + t • v` and then checks
`q ∈ boundary`. For the unit square we can prove this membership under geometric hypotheses:
- the velocity points inward at the current boundary point, and
- the next impact is not a corner hit (`tx ≠ ty` when both wall-hit times exist).
-/

def Good (s : CollisionState) : Prop :=
  Inward s.pos s.vel ∧
  ¬ IsCorner s.pos ∧
  match timeToX? s.pos s.vel, timeToY? s.pos s.vel with
  | some tx, some ty => tx ≠ ty
  | _, _ => True

private theorem eq_zero_of_x_eq_zero_of_y_eq_zero (v : V) (hx : x v = 0) (hy : y v = 0) : v = 0 := by
  ext i
  cases i using Fin.cases with
  | zero => simpa [UnitSquare.x] using hx
  | succ j =>
    cases j using Fin.cases with
    | zero => simpa [UnitSquare.y] using hy
    | succ k => exact (Fin.elim0 k)

private theorem timeToX?_eq_none_iff (p v : V) : timeToX? p v = none ↔ x v = 0 := by
  unfold timeToX?
  by_cases hxpos : 0 < x v
  · simp [hxpos, hxpos.ne']
  · by_cases hxneg : x v < 0
    · have hxpos' : ¬0 < x v := not_lt_of_ge (le_of_lt hxneg)
      simp [hxpos', hxneg, hxneg.ne]
    · have hxle : x v ≤ 0 := le_of_not_gt hxpos
      have hxge : 0 ≤ x v := le_of_not_gt hxneg
      have hx0 : x v = 0 := le_antisymm hxle hxge
      simp [hx0]

private theorem timeToY?_eq_none_iff (p v : V) : timeToY? p v = none ↔ y v = 0 := by
  unfold timeToY?
  by_cases hypos : 0 < y v
  · simp [hypos, hypos.ne']
  · by_cases hyneg : y v < 0
    · have hypos' : ¬0 < y v := not_lt_of_ge (le_of_lt hyneg)
      simp [hypos', hyneg, hyneg.ne]
    · have hyle : y v ≤ 0 := le_of_not_gt hypos
      have hyge : 0 ≤ y v := le_of_not_gt hyneg
      have hy0 : y v = 0 := le_antisymm hyle hyge
      simp [hy0]

private theorem timeToX?_some_cases {p v : V} {t : ℝ} (h : timeToX? p v = some t) :
    (0 < x v ∧ t = (1 - x p) / x v) ∨ (x v < 0 ∧ t = (0 - x p) / x v) := by
  unfold timeToX? at h
  by_cases hxpos : 0 < x v
  · have hxneg : ¬x v < 0 := not_lt_of_ge (le_of_lt hxpos)
    have h' : some ((1 - x p) / x v) = some t := by
      simpa [hxpos, hxneg] using h
    left
    exact ⟨hxpos, (Option.some.inj h').symm⟩
  · by_cases hxneg : x v < 0
    · right
      refine ⟨hxneg, ?_⟩
      have hxpos' : ¬0 < x v := not_lt_of_ge (le_of_lt hxneg)
      have h' : some ((0 - x p) / x v) = some t := by
        simpa [hxpos', hxneg] using h
      exact (Option.some.inj h').symm
    · have hxle : x v ≤ 0 := le_of_not_gt hxpos
      have hxge : 0 ≤ x v := le_of_not_gt hxneg
      have hx0 : x v = 0 := le_antisymm hxle hxge
      simp [hx0] at h

private theorem timeToY?_some_cases {p v : V} {t : ℝ} (h : timeToY? p v = some t) :
    (0 < y v ∧ t = (1 - y p) / y v) ∨ (y v < 0 ∧ t = (0 - y p) / y v) := by
  unfold timeToY? at h
  by_cases hypos : 0 < y v
  · have hyneg : ¬y v < 0 := not_lt_of_ge (le_of_lt hypos)
    have h' : some ((1 - y p) / y v) = some t := by
      simpa [hypos, hyneg] using h
    left
    exact ⟨hypos, (Option.some.inj h').symm⟩
  · by_cases hyneg : y v < 0
    · right
      refine ⟨hyneg, ?_⟩
      have hypos' : ¬0 < y v := not_lt_of_ge (le_of_lt hyneg)
      have h' : some ((0 - y p) / y v) = some t := by
        simpa [hypos', hyneg] using h
      exact (Option.some.inj h').symm
    · have hyle : y v ≤ 0 := le_of_not_gt hypos
      have hyge : 0 ≤ y v := le_of_not_gt hyneg
      have hy0 : y v = 0 := le_antisymm hyle hyge
      simp [hy0] at h

private theorem nextHit?_eq_some_hitX {p v : V} {t : ℝ}
    (h : nextHit? p v = some (HitKind.hitX, t)) :
    timeToX? p v = some t ∧ (timeToY? p v = none ∨ ∃ ty, timeToY? p v = some ty ∧ t < ty) := by
  classical
  unfold nextHit? at h
  cases hx : timeToX? p v <;> cases hy : timeToY? p v <;> simp [hx, hy] at h
  · cases h
    exact ⟨rfl, Or.inl rfl⟩
  · -- both `some`: in this branch `tx < ty`.
    rename_i tx ty
    by_cases hlt : tx < ty
    · have h' : some (HitKind.hitX, tx) = some (HitKind.hitX, t) := by
        simpa [hlt, not_lt_of_gt hlt] using h
      have ht : t = tx := (congrArg Prod.snd (Option.some.inj h')).symm
      subst ht
      refine ⟨rfl, Or.inr ?_⟩
      exact ⟨ty, rfl, hlt⟩
    · have : False := by
        -- If `¬tx < ty`, the result cannot be a `hitX`.
        by_cases hgt : ty < tx
        · simp [hlt, hgt] at h
        · simp [hlt, hgt] at h
      exact False.elim this

private theorem nextHit?_eq_some_hitY {p v : V} {t : ℝ}
    (h : nextHit? p v = some (HitKind.hitY, t)) :
    timeToY? p v = some t ∧ (timeToX? p v = none ∨ ∃ tx, timeToX? p v = some tx ∧ t < tx) := by
  classical
  unfold nextHit? at h
  cases hx : timeToX? p v <;> cases hy : timeToY? p v <;> simp [hx, hy] at h
  · cases h
    exact ⟨rfl, Or.inl rfl⟩
  · rename_i tx ty
    by_cases hlt : tx < ty
    · simp [hlt] at h
    · by_cases hgt : ty < tx
      · have h' : some (HitKind.hitY, ty) = some (HitKind.hitY, t) := by
          simpa [hlt, hgt] using h
        have ht : t = ty := (congrArg Prod.snd (Option.some.inj h')).symm
        subst ht
        refine ⟨rfl, Or.inr ?_⟩
        exact ⟨tx, rfl, hgt⟩
      · simp [hlt, hgt] at h

private theorem x_eq_zero_or_one_of_timeToX? {p v : V} {t : ℝ}
    (h : timeToX? p v = some t) : x (p + t • v) = 0 ∨ x (p + t • v) = 1 := by
  rcases timeToX?_some_cases (p := p) (v := v) (t := t) h with ⟨hxpos, rfl⟩ | ⟨hxneg, rfl⟩
  · right
    have hxne : x v ≠ 0 := ne_of_gt hxpos
    simp [div_eq_mul_inv, hxne]
  · left
    have hxne : x v ≠ 0 := ne_of_lt hxneg
    simp [div_eq_mul_inv, hxne]

private theorem y_eq_zero_or_one_of_timeToY? {p v : V} {t : ℝ}
    (h : timeToY? p v = some t) : y (p + t • v) = 0 ∨ y (p + t • v) = 1 := by
  rcases timeToY?_some_cases (p := p) (v := v) (t := t) h with ⟨hypos, rfl⟩ | ⟨hyneg, rfl⟩
  · right
    have hyne : y v ≠ 0 := ne_of_gt hypos
    simp [div_eq_mul_inv, hyne]
  · left
    have hyne : y v ≠ 0 := ne_of_lt hyneg
    simp [div_eq_mul_inv, hyne]

private theorem timeToX?_pos_of_inward {p v : V} (hp : p ∈ boundary) (hin : Inward p v)
    {t : ℝ} (ht : timeToX? p v = some t) : 0 < t := by
  have hxBounds : 0 ≤ x p ∧ x p ≤ 1 := x_bounds_of_boundary hp
  rcases timeToX?_some_cases (p := p) (v := v) (t := t) ht with ⟨hxpos, rfl⟩ | ⟨hxneg, rfl⟩
  · -- `0 < x v`, so `x p ≠ 1` by inwardness/corner exclusion
    have hx1 : x p ≠ 1 := by
      intro hx1
      have : x p = 1 ∨ x p = 0 := Or.inl hx1
      -- if `x p = 1`, inward requires `x v < 0`, contradiction.
      exact (not_lt_of_gt hxpos) ((hin.2.1) hx1)
    have hxlt1 : x p < 1 := lt_of_le_of_ne hxBounds.2 hx1
    have hnum : 0 < (1 - x p) := by linarith
    exact div_pos hnum hxpos
  · -- `x v < 0`, so `x p ≠ 0` by inwardness/corner exclusion
    have hx0 : x p ≠ 0 := by
      intro hx0
      exact (not_lt_of_gt (hin.1 hx0)) hxneg
    have hxgt0 : 0 < x p := lt_of_le_of_ne hxBounds.1 (Ne.symm hx0)
    have hnum : (0 - x p) < 0 := by linarith
    exact div_pos_of_neg_of_neg hnum hxneg

private theorem timeToY?_pos_of_inward {p v : V} (hp : p ∈ boundary) (hin : Inward p v)
    {t : ℝ} (ht : timeToY? p v = some t) : 0 < t := by
  have hyBounds : 0 ≤ y p ∧ y p ≤ 1 := y_bounds_of_boundary hp
  rcases timeToY?_some_cases (p := p) (v := v) (t := t) ht with ⟨hypos, rfl⟩ | ⟨hyneg, rfl⟩
  · have hy1 : y p ≠ 1 := by
      intro hy1
      exact (not_lt_of_gt hypos) ((hin.2.2.2) hy1)
    have hylt1 : y p < 1 := lt_of_le_of_ne hyBounds.2 hy1
    have hnum : 0 < (1 - y p) := by linarith
    exact div_pos hnum hypos
  · have hy0 : y p ≠ 0 := by
      intro hy0
      exact (not_lt_of_gt (hin.2.2.1 hy0)) hyneg
    have hygt0 : 0 < y p := lt_of_le_of_ne hyBounds.1 (Ne.symm hy0)
    have hnum : (0 - y p) < 0 := by linarith
    exact div_pos_of_neg_of_neg hnum hyneg

private theorem nextHit?_exists_of_good (s : CollisionState) (hs : Good s) :
    ∃ hk t, nextHit? s.pos s.vel = some (hk, t) := by
  classical
  -- Case split on availability of wall-hit times.
  cases htx : timeToX? s.pos s.vel with
  | none =>
    cases hty : timeToY? s.pos s.vel with
    | none =>
      -- both times are `none` ⇒ both velocity components are zero ⇒ contradiction with `vel_ne_zero`.
      have hx0 : x s.vel = 0 := (timeToX?_eq_none_iff (p := s.pos) (v := s.vel)).1 htx
      have hy0 : y s.vel = 0 := (timeToY?_eq_none_iff (p := s.pos) (v := s.vel)).1 hty
      exact False.elim (s.vel_ne_zero (eq_zero_of_x_eq_zero_of_y_eq_zero s.vel hx0 hy0))
    | some ty =>
      refine ⟨HitKind.hitY, ty, ?_⟩
      simp [nextHit?, htx, hty]
  | some tx =>
    cases hty : timeToY? s.pos s.vel with
    | none =>
      refine ⟨HitKind.hitX, tx, ?_⟩
      simp [nextHit?, htx, hty]
    | some ty =>
      have hne : tx ≠ ty := by simpa [htx, hty] using hs.2.2
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · refine ⟨HitKind.hitX, tx, ?_⟩
        simp [nextHit?, htx, hty, hlt]
      · refine ⟨HitKind.hitY, ty, ?_⟩
        simp [nextHit?, htx, hty, hgt, not_lt_of_gt hgt]

private theorem y_mem_Icc_of_time_le_timeToY? {p v : V} {t ty : ℝ}
    (hp : p ∈ region) (ht0 : 0 ≤ t) (hty : timeToY? p v = some ty) (htle : t ≤ ty) :
    y (p + t • v) ∈ Set.Icc (0 : ℝ) 1 := by
  have hyBounds : 0 ≤ y p ∧ y p ≤ 1 := (mem_region_iff p).1 hp |>.2
  rcases timeToY?_some_cases (p := p) (v := v) (t := ty) hty with ⟨hypos, htyeq⟩ | ⟨hyneg, htyeq⟩
  · have hy0 : 0 ≤ y v := le_of_lt hypos
    have hmul : t * y v ≤ (1 - y p) := by
      have := mul_le_mul_of_nonneg_right htle hy0
      simpa [htyeq, div_eq_mul_inv, mul_assoc, hypos.ne'] using this
    have hupp : y (p + t • v) ≤ 1 := by
      simp
      linarith
    have hlow : 0 ≤ y (p + t • v) := by
      have htmul : 0 ≤ t * y v := mul_nonneg ht0 hy0
      simp
      linarith [hyBounds.1, htmul]
    exact ⟨hlow, hupp⟩
  · have hy0 : y v ≤ 0 := le_of_lt hyneg
    have hmul : (0 - y p) ≤ t * y v := by
      have := mul_le_mul_of_nonpos_right htle hy0
      simpa [htyeq, div_eq_mul_inv, mul_assoc, hyneg.ne] using this
    have hlow : 0 ≤ y (p + t • v) := by
      simp
      linarith
    have hupp : y (p + t • v) ≤ 1 := by
      have htmul : t * y v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hy0
      simp
      linarith [hyBounds.2, htmul]
    exact ⟨hlow, hupp⟩

private theorem x_mem_Icc_of_time_le_timeToX? {p v : V} {t tx : ℝ}
    (hp : p ∈ region) (ht0 : 0 ≤ t) (htx : timeToX? p v = some tx) (htle : t ≤ tx) :
    x (p + t • v) ∈ Set.Icc (0 : ℝ) 1 := by
  have hxBounds : 0 ≤ x p ∧ x p ≤ 1 := (mem_region_iff p).1 hp |>.1
  rcases timeToX?_some_cases (p := p) (v := v) (t := tx) htx with ⟨hxpos, htxeq⟩ | ⟨hxneg, htxeq⟩
  · have hx0 : 0 ≤ x v := le_of_lt hxpos
    have hmul : t * x v ≤ (1 - x p) := by
      have := mul_le_mul_of_nonneg_right htle hx0
      simpa [htxeq, div_eq_mul_inv, mul_assoc, hxpos.ne'] using this
    have hupp : x (p + t • v) ≤ 1 := by
      simp
      linarith
    have hlow : 0 ≤ x (p + t • v) := by
      have htmul : 0 ≤ t * x v := mul_nonneg ht0 hx0
      simp
      linarith [hxBounds.1, htmul]
    exact ⟨hlow, hupp⟩
  · have hx0 : x v ≤ 0 := le_of_lt hxneg
    have hmul : (0 - x p) ≤ t * x v := by
      have := mul_le_mul_of_nonpos_right htle hx0
      simpa [htxeq, div_eq_mul_inv, mul_assoc, hxneg.ne] using this
    have hlow : 0 ≤ x (p + t • v) := by
      simp
      linarith
    have hupp : x (p + t • v) ≤ 1 := by
      have htmul : t * x v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hx0
      simp
      linarith [hxBounds.2, htmul]
    exact ⟨hlow, hupp⟩

private lemma eX_eq_single : UnitSquare.eX = EuclideanSpace.single (ι := Fin 2) 0 (1 : ℝ) := by
  ext i
  cases i using Fin.cases with
  | zero =>
    simp [UnitSquare.eX, EuclideanSpace.single_apply]
  | succ j =>
    cases j using Fin.cases with
    | zero =>
      simp [UnitSquare.eX, EuclideanSpace.single_apply]
    | succ k =>
      exact (Fin.elim0 k)

private lemma eY_eq_single : UnitSquare.eY = EuclideanSpace.single (ι := Fin 2) 1 (1 : ℝ) := by
  ext i
  cases i using Fin.cases with
  | zero =>
    simp [UnitSquare.eY, EuclideanSpace.single_apply]
  | succ j =>
    cases j using Fin.cases with
    | zero =>
      simp [UnitSquare.eY, EuclideanSpace.single_apply]
    | succ k =>
      exact (Fin.elim0 k)

private lemma inner_eX (v : V) : inner ℝ UnitSquare.eX v = x v := by
  -- `eX` is `EuclideanSpace.single 0 1`, so the inner product extracts the 0th coordinate.
  simp [eX_eq_single, UnitSquare.x, EuclideanSpace.inner_single_left]

private lemma inner_eY (v : V) : inner ℝ UnitSquare.eY v = y v := by
  simp [eY_eq_single, UnitSquare.y, EuclideanSpace.inner_single_left]

private lemma norm_eX : ‖(UnitSquare.eX : V)‖ = (1 : ℝ) := by
  simp [eX_eq_single]

private lemma norm_eY : ‖(UnitSquare.eY : V)‖ = (1 : ℝ) := by
  simp [eY_eq_single]

private lemma reflect_eX_x (v : V) : x (reflect UnitSquare.eX v) = -x v := by
  -- Use the explicit reflection formula specialized to the standard basis vector `eX`.
  have horth :
      ((ℝ ∙ UnitSquare.eX)ᗮ).reflection v = -((ℝ ∙ UnitSquare.eX).reflection v) := by
    simpa using (Submodule.reflection_orthogonal_apply (K := (ℝ ∙ UnitSquare.eX)) (v := v))
  -- Expand `reflect` and the reflection-in-span formula, then compute the `x` coordinate.
  -- `eX` has unit norm, and `⟪eX, v⟫ = x v`.
  have hform : reflect UnitSquare.eX v = v - 2 • (x v) • (UnitSquare.eX : V) := by
    -- `Kᗮ.reflection v = -K.reflection v`, and `K.reflection v` has a closed form for `K = span`.
    calc
      reflect UnitSquare.eX v
          = -((ℝ ∙ UnitSquare.eX).reflection v) := by
              simpa [Billiards.reflect] using horth
      _ = - (2 • (inner ℝ UnitSquare.eX v / ((‖UnitSquare.eX‖ : ℝ) ^ 2)) • UnitSquare.eX - v) := by
              simp [Submodule.reflection_singleton_apply]
      _ = v - 2 • (inner ℝ UnitSquare.eX v / ((‖UnitSquare.eX‖ : ℝ) ^ 2)) • UnitSquare.eX := by
              abel
      _ = v - 2 • (x v) • (UnitSquare.eX : V) := by
              simp [inner_eX, norm_eX]
  -- Now take the `x` coordinate.
  -- The `x` coordinate of `eX` is 1.
  have hx : x (UnitSquare.eX : V) = (1 : ℝ) := UnitSquare.eX_x
  calc
    x (reflect UnitSquare.eX v)
        = x (v - 2 • (x v) • (UnitSquare.eX : V)) := by
            simp [hform]
    _ = -x v := by
            simp [sub_eq_add_neg, hx]
            ring

private lemma reflect_eX_y (v : V) : y (reflect UnitSquare.eX v) = y v := by
  have horth :
      ((ℝ ∙ UnitSquare.eX)ᗮ).reflection v = -((ℝ ∙ UnitSquare.eX).reflection v) := by
    simpa using (Submodule.reflection_orthogonal_apply (K := (ℝ ∙ UnitSquare.eX)) (v := v))
  have hform : reflect UnitSquare.eX v = v - 2 • (x v) • (UnitSquare.eX : V) := by
    calc
      reflect UnitSquare.eX v
          = -((ℝ ∙ UnitSquare.eX).reflection v) := by
              simpa [Billiards.reflect] using horth
      _ = - (2 • (inner ℝ UnitSquare.eX v / ((‖UnitSquare.eX‖ : ℝ) ^ 2)) • UnitSquare.eX - v) := by
              simp [Submodule.reflection_singleton_apply]
      _ = v - 2 • (inner ℝ UnitSquare.eX v / ((‖UnitSquare.eX‖ : ℝ) ^ 2)) • UnitSquare.eX := by
              abel
      _ = v - 2 • (x v) • (UnitSquare.eX : V) := by
              simp [inner_eX, norm_eX]
  have hy : y (UnitSquare.eX : V) = (0 : ℝ) := UnitSquare.eX_y
  -- `eX` has no `y` component, so reflecting across `eX` preserves the `y` coordinate.
  calc
    y (reflect UnitSquare.eX v)
        = y (v - 2 • (x v) • (UnitSquare.eX : V)) := by
            simp [hform]
    _ = y v := by
            simp [sub_eq_add_neg, hy]

private lemma reflect_eY_y (v : V) : y (reflect UnitSquare.eY v) = -y v := by
  have horth :
      ((ℝ ∙ UnitSquare.eY)ᗮ).reflection v = -((ℝ ∙ UnitSquare.eY).reflection v) := by
    simpa using (Submodule.reflection_orthogonal_apply (K := (ℝ ∙ UnitSquare.eY)) (v := v))
  have hform : reflect UnitSquare.eY v = v - 2 • (y v) • (UnitSquare.eY : V) := by
    calc
      reflect UnitSquare.eY v
          = -((ℝ ∙ UnitSquare.eY).reflection v) := by
              simpa [Billiards.reflect] using horth
      _ = - (2 • (inner ℝ UnitSquare.eY v / ((‖UnitSquare.eY‖ : ℝ) ^ 2)) • UnitSquare.eY - v) := by
              simp [Submodule.reflection_singleton_apply]
      _ = v - 2 • (inner ℝ UnitSquare.eY v / ((‖UnitSquare.eY‖ : ℝ) ^ 2)) • UnitSquare.eY := by
              abel
      _ = v - 2 • (y v) • (UnitSquare.eY : V) := by
              simp [inner_eY, norm_eY]
  have hy : y (UnitSquare.eY : V) = (1 : ℝ) := UnitSquare.eY_y
  calc
    y (reflect UnitSquare.eY v)
        = y (v - 2 • (y v) • (UnitSquare.eY : V)) := by
            simp [hform]
    _ = -y v := by
            simp [sub_eq_add_neg, hy]
            ring

private lemma reflect_eY_x (v : V) : x (reflect UnitSquare.eY v) = x v := by
  have horth :
      ((ℝ ∙ UnitSquare.eY)ᗮ).reflection v = -((ℝ ∙ UnitSquare.eY).reflection v) := by
    simpa using (Submodule.reflection_orthogonal_apply (K := (ℝ ∙ UnitSquare.eY)) (v := v))
  have hform : reflect UnitSquare.eY v = v - 2 • (y v) • (UnitSquare.eY : V) := by
    calc
      reflect UnitSquare.eY v
          = -((ℝ ∙ UnitSquare.eY).reflection v) := by
              simpa [Billiards.reflect] using horth
      _ = - (2 • (inner ℝ UnitSquare.eY v / ((‖UnitSquare.eY‖ : ℝ) ^ 2)) • UnitSquare.eY - v) := by
              simp [Submodule.reflection_singleton_apply]
      _ = v - 2 • (inner ℝ UnitSquare.eY v / ((‖UnitSquare.eY‖ : ℝ) ^ 2)) • UnitSquare.eY := by
              abel
      _ = v - 2 • (y v) • (UnitSquare.eY : V) := by
              simp [inner_eY, norm_eY]
  have hx : x (UnitSquare.eY : V) = (0 : ℝ) := UnitSquare.eY_x
  calc
    x (reflect UnitSquare.eY v)
        = x (v - 2 • (y v) • (UnitSquare.eY : V)) := by
            simp [hform]
    _ = x v := by
            simp [sub_eq_add_neg, hx]

theorem reflect_ne_zero {n v : V} (hv : v ≠ 0) : reflect n v ≠ 0 := by
  intro h
  have hnorm : ‖v‖ = 0 := by
    have : ‖reflect n v‖ = 0 := by simp [h]
    simpa [norm_reflect] using this
  exact hv (by simpa using (norm_eq_zero.mp hnorm))

/-- The unit-square billiard map as a **partial** function on boundary states.

This is staged: the definition is deterministic and produces a `UnitSquare.table.Step` whenever it
succeeds. Totality/uniqueness properties (and corner/tangency exclusions) are WS7.3 followups. -/
def next? (s : CollisionState) : Option CollisionState := by
  classical
  match nextHit? s.pos s.vel with
  | none => exact none
  | some (_hk, t) =>
      if ht : 0 < t then
        let q : V := s.pos + t • s.vel
        if hq : q ∈ boundary then
          let v' : V := reflect (UnitSquare.normal ⟨q, hq⟩) s.vel
          exact some
            { pos := q
              pos_mem := hq
              vel := v'
              vel_ne_zero :=
                reflect_ne_zero (n := UnitSquare.normal ⟨q, hq⟩) (v := s.vel) s.vel_ne_zero }
        else
          exact none
      else
        exact none

def stepRel (s s' : CollisionState) : Prop :=
  next? s = some s'

theorem next?_eq_some_of_good (s : CollisionState) (hs : Good s) :
    ∃ s' : CollisionState, next? s = some s' := by
  classical
  have hin : Inward s.pos s.vel := hs.1
  have hpreg : s.pos ∈ region := boundary_subset_region s.pos_mem
  rcases nextHit?_exists_of_good s hs with ⟨hk, t, hhit⟩
  have ht : 0 < t := by
    cases hk with
    | hitX =>
      have htx : timeToX? s.pos s.vel = some t :=
        (nextHit?_eq_some_hitX (p := s.pos) (v := s.vel) (t := t) (by simpa using hhit)).1
      exact timeToX?_pos_of_inward (p := s.pos) (v := s.vel) s.pos_mem hin htx
    | hitY =>
      have hty : timeToY? s.pos s.vel = some t :=
        (nextHit?_eq_some_hitY (p := s.pos) (v := s.vel) (t := t) (by simpa using hhit)).1
      exact timeToY?_pos_of_inward (p := s.pos) (v := s.vel) s.pos_mem hin hty
  have hq : s.pos + t • s.vel ∈ boundary := by
    cases hk with
    | hitX =>
      have h' : nextHit? s.pos s.vel = some (HitKind.hitX, t) := by simpa using hhit
      rcases nextHit?_eq_some_hitX (p := s.pos) (v := s.vel) (t := t) h' with ⟨htx, hyAlt⟩
      have hxwall : x (s.pos + t • s.vel) = 0 ∨ x (s.pos + t • s.vel) = 1 :=
        x_eq_zero_or_one_of_timeToX? (p := s.pos) (v := s.vel) (t := t) htx
      have hyIcc : y (s.pos + t • s.vel) ∈ Set.Icc (0 : ℝ) 1 := by
        cases hyAlt with
        | inl hnone =>
          have hyv0 : y s.vel = 0 := (timeToY?_eq_none_iff (p := s.pos) (v := s.vel)).1 hnone
          have hyBounds : 0 ≤ y s.pos ∧ y s.pos ≤ 1 := (mem_region_iff s.pos).1 hpreg |>.2
          simpa [y_add_smul, hyv0] using hyBounds
        | inr hsome =>
          rcases hsome with ⟨ty, hty, htlt⟩
          exact
            y_mem_Icc_of_time_le_timeToY? (p := s.pos) (v := s.vel) (t := t) (ty := ty)
              hpreg (le_of_lt ht) hty (le_of_lt htlt)
      have hxIcc : x (s.pos + t • s.vel) ∈ Set.Icc (0 : ℝ) 1 := by
        rcases hxwall with hx0 | hx1
        · simp [hx0]
        · simp [hx1]
      have hreg : (s.pos + t • s.vel) ∈ region :=
        (mem_region_iff (s.pos + t • s.vel)).2 ⟨hxIcc, hyIcc⟩
      refine ⟨hreg, ?_⟩
      rcases hxwall with hx0 | hx1
      · exact Or.inl hx0
      · exact Or.inr (Or.inl hx1)
    | hitY =>
      have h' : nextHit? s.pos s.vel = some (HitKind.hitY, t) := by simpa using hhit
      rcases nextHit?_eq_some_hitY (p := s.pos) (v := s.vel) (t := t) h' with ⟨hty, hxAlt⟩
      have hywall : y (s.pos + t • s.vel) = 0 ∨ y (s.pos + t • s.vel) = 1 :=
        y_eq_zero_or_one_of_timeToY? (p := s.pos) (v := s.vel) (t := t) hty
      have hxIcc : x (s.pos + t • s.vel) ∈ Set.Icc (0 : ℝ) 1 := by
        cases hxAlt with
        | inl hnone =>
          have hxv0 : x s.vel = 0 := (timeToX?_eq_none_iff (p := s.pos) (v := s.vel)).1 hnone
          have hxBounds : 0 ≤ x s.pos ∧ x s.pos ≤ 1 := (mem_region_iff s.pos).1 hpreg |>.1
          simpa [x_add_smul, hxv0] using hxBounds
        | inr hsome =>
          rcases hsome with ⟨tx, htx, htlt⟩
          exact
            x_mem_Icc_of_time_le_timeToX? (p := s.pos) (v := s.vel) (t := t) (tx := tx)
              hpreg (le_of_lt ht) htx (le_of_lt htlt)
      have hyIcc : y (s.pos + t • s.vel) ∈ Set.Icc (0 : ℝ) 1 := by
        rcases hywall with hy0 | hy1
        · simp [hy0]
        · simp [hy1]
      have hreg : (s.pos + t • s.vel) ∈ region :=
        (mem_region_iff (s.pos + t • s.vel)).2 ⟨hxIcc, hyIcc⟩
      refine ⟨hreg, ?_⟩
      rcases hywall with hy0 | hy1
      · exact Or.inr (Or.inr (Or.inl hy0))
      · exact Or.inr (Or.inr (Or.inr hy1))
  refine ⟨{ pos := s.pos + t • s.vel
            pos_mem := hq
            vel := reflect (UnitSquare.normal ⟨s.pos + t • s.vel, hq⟩) s.vel
            vel_ne_zero :=
              reflect_ne_zero (n := UnitSquare.normal ⟨s.pos + t • s.vel, hq⟩) (v := s.vel) s.vel_ne_zero }, ?_⟩
  simp [next?, hhit, ht, hq]

/-!
## WS7.3: a check-free successor map on “good” states

The definition of `next?` is staged: after computing `q := p + t • v` it checks `q ∈ boundary`
before producing the next collision. For the unit square, the membership check is redundant on
`Good` states: it follows from the explicit `nextHit?` wall-time computation.
-/

private theorem pos_mem_boundary_of_nextHit_of_good (s : CollisionState) (hs : Good s) {hk : HitKind} {t : ℝ}
    (hhit : nextHit? s.pos s.vel = some (hk, t)) :
    0 < t ∧ s.pos + t • s.vel ∈ boundary := by
  classical
  have hin : Inward s.pos s.vel := hs.1
  have hpreg : s.pos ∈ region := boundary_subset_region s.pos_mem
  have ht : 0 < t := by
    cases hk with
    | hitX =>
      have htx : timeToX? s.pos s.vel = some t :=
        (nextHit?_eq_some_hitX (p := s.pos) (v := s.vel) (t := t) (by simpa using hhit)).1
      exact timeToX?_pos_of_inward (p := s.pos) (v := s.vel) s.pos_mem hin htx
    | hitY =>
      have hty : timeToY? s.pos s.vel = some t :=
        (nextHit?_eq_some_hitY (p := s.pos) (v := s.vel) (t := t) (by simpa using hhit)).1
      exact timeToY?_pos_of_inward (p := s.pos) (v := s.vel) s.pos_mem hin hty
  have hq : s.pos + t • s.vel ∈ boundary := by
    cases hk with
    | hitX =>
      rcases nextHit?_eq_some_hitX (p := s.pos) (v := s.vel) (t := t) (by simpa using hhit) with ⟨htx, hyAlt⟩
      have hxwall : x (s.pos + t • s.vel) = 0 ∨ x (s.pos + t • s.vel) = 1 :=
        x_eq_zero_or_one_of_timeToX? (p := s.pos) (v := s.vel) (t := t) htx
      have hyIcc : y (s.pos + t • s.vel) ∈ Set.Icc (0 : ℝ) 1 := by
        cases hyAlt with
        | inl hnone =>
          have hyv0 : y s.vel = 0 := (timeToY?_eq_none_iff (p := s.pos) (v := s.vel)).1 hnone
          have hyBounds : 0 ≤ y s.pos ∧ y s.pos ≤ 1 := (mem_region_iff s.pos).1 hpreg |>.2
          simpa [y_add_smul, hyv0] using hyBounds
        | inr hsome =>
          rcases hsome with ⟨ty, hty, htlt⟩
          exact
            y_mem_Icc_of_time_le_timeToY? (p := s.pos) (v := s.vel) (t := t) (ty := ty)
              hpreg (le_of_lt ht) hty (le_of_lt htlt)
      have hxIcc : x (s.pos + t • s.vel) ∈ Set.Icc (0 : ℝ) 1 := by
        rcases hxwall with hx0 | hx1
        · simp [hx0]
        · simp [hx1]
      have hreg : (s.pos + t • s.vel) ∈ region :=
        (mem_region_iff (s.pos + t • s.vel)).2 ⟨hxIcc, hyIcc⟩
      refine ⟨hreg, ?_⟩
      rcases hxwall with hx0 | hx1
      · exact Or.inl hx0
      · exact Or.inr (Or.inl hx1)
    | hitY =>
      rcases nextHit?_eq_some_hitY (p := s.pos) (v := s.vel) (t := t) (by simpa using hhit) with ⟨hty, hxAlt⟩
      have hywall : y (s.pos + t • s.vel) = 0 ∨ y (s.pos + t • s.vel) = 1 :=
        y_eq_zero_or_one_of_timeToY? (p := s.pos) (v := s.vel) (t := t) hty
      have hxIcc : x (s.pos + t • s.vel) ∈ Set.Icc (0 : ℝ) 1 := by
        cases hxAlt with
        | inl hnone =>
          have hxv0 : x s.vel = 0 := (timeToX?_eq_none_iff (p := s.pos) (v := s.vel)).1 hnone
          have hxBounds : 0 ≤ x s.pos ∧ x s.pos ≤ 1 := (mem_region_iff s.pos).1 hpreg |>.1
          simpa [x_add_smul, hxv0] using hxBounds
        | inr hsome =>
          rcases hsome with ⟨tx, htx, htlt⟩
          exact
            x_mem_Icc_of_time_le_timeToX? (p := s.pos) (v := s.vel) (t := t) (tx := tx)
              hpreg (le_of_lt ht) htx (le_of_lt htlt)
      have hyIcc : y (s.pos + t • s.vel) ∈ Set.Icc (0 : ℝ) 1 := by
        rcases hywall with hy0 | hy1
        · simp [hy0]
        · simp [hy1]
      have hreg : (s.pos + t • s.vel) ∈ region :=
        (mem_region_iff (s.pos + t • s.vel)).2 ⟨hxIcc, hyIcc⟩
      refine ⟨hreg, ?_⟩
      rcases hywall with hy0 | hy1
      · exact Or.inr (Or.inr (Or.inl hy0))
      · exact Or.inr (Or.inr (Or.inr hy1))
  exact ⟨ht, hq⟩

private theorem nextHit?_exists_pair_of_good (s : CollisionState) (hs : Good s) :
    ∃ ht : HitKind × ℝ, nextHit? s.pos s.vel = some ht := by
  rcases nextHit?_exists_of_good s hs with ⟨hk, t, hhit⟩
  exact ⟨(hk, t), by simpa using hhit⟩

private noncomputable def nextHitData (s : CollisionState) (hs : Good s) : HitKind × ℝ :=
  Classical.choose (nextHit?_exists_pair_of_good s hs)

private theorem nextHit?_eq_some_nextHitData (s : CollisionState) (hs : Good s) :
    nextHit? s.pos s.vel = some (nextHitData s hs) :=
  Classical.choose_spec (nextHit?_exists_pair_of_good s hs)

/-- A successor collision state on `Good` inputs, defined without the staged `q ∈ boundary` check. -/
noncomputable def nextGood (s : CollisionState) (hs : Good s) : CollisionState := by
  classical
  let ht := nextHitData s hs
  let q : V := s.pos + ht.2 • s.vel
  have htpos : 0 < ht.2 ∧ q ∈ boundary := by
    have : nextHit? s.pos s.vel = some ht := nextHit?_eq_some_nextHitData s hs
    simpa [q] using (pos_mem_boundary_of_nextHit_of_good (s := s) (hs := hs) (hk := ht.1) (t := ht.2) this)
  have hq : q ∈ boundary := htpos.2
  exact
    { pos := q
      pos_mem := hq
      vel := reflect (UnitSquare.normal ⟨q, hq⟩) s.vel
      vel_ne_zero :=
        reflect_ne_zero (n := UnitSquare.normal ⟨q, hq⟩) (v := s.vel) s.vel_ne_zero }

theorem next?_eq_some_nextGood (s : CollisionState) (hs : Good s) :
    next? s = some (nextGood s hs) := by
  classical
  let ht := nextHitData s hs
  let q : V := s.pos + ht.2 • s.vel
  have hhit : nextHit? s.pos s.vel = some ht := nextHit?_eq_some_nextHitData s hs
  have htpos : 0 < ht.2 ∧ q ∈ boundary := by
    simpa [q] using
      (pos_mem_boundary_of_nextHit_of_good (s := s) (hs := hs) (hk := ht.1) (t := ht.2) (by simpa using hhit))
  have hq : q ∈ boundary := htpos.2
  have ht' : 0 < ht.2 := htpos.1
  simp [next?, nextGood, ht, hhit, ht', q, hq]

theorem next?_existsUnique_of_good (s : CollisionState) (hs : Good s) :
    ∃! s' : CollisionState, next? s = some s' := by
  refine ⟨nextGood s hs, next?_eq_some_nextGood s hs, ?_⟩
  intro t ht
  have : (some (nextGood s hs) : Option CollisionState) = some t := by
    simpa [next?_eq_some_nextGood s hs] using ht
  exact (Option.some.inj this).symm

theorem existsUnique_stepRel_of_good (s : CollisionState) (hs : Good s) :
    ∃! s' : CollisionState, stepRel s s' := by
  rcases next?_eq_some_of_good s hs with ⟨s', hs'⟩
  refine ⟨s', ?_, ?_⟩
  · simpa [stepRel] using hs'
  · intro t ht
    unfold stepRel at ht
    have : (some s' : Option CollisionState) = some t := by
      simpa [hs'] using ht
    exact (Option.some.inj this).symm

def Reaches (s s' : CollisionState) : Prop :=
  Relation.ReflTransGen stepRel s s'

@[simp] theorem Reaches.refl (s : CollisionState) : Reaches s s :=
  Relation.ReflTransGen.refl

theorem Reaches.trans {s₁ s₂ s₃ : CollisionState} :
    Reaches s₁ s₂ → Reaches s₂ s₃ → Reaches s₁ s₃ :=
  Relation.ReflTransGen.trans

/-- Iterate the partial billiard map `next?` `n` times (returns `none` if any step is undefined). -/
def nextIter? : Nat → CollisionState → Option CollisionState
  | 0, s => some s
  | n + 1, s =>
      match nextIter? n s with
      | none => none
      | some s' => next? s'

@[simp] theorem nextIter?_zero (s : CollisionState) : nextIter? 0 s = some s := rfl

@[simp] theorem nextIter?_succ (n : Nat) (s : CollisionState) :
    nextIter? (n + 1) s =
      match nextIter? n s with
      | none => none
      | some s' => next? s' :=
  rfl

theorem Reaches.of_nextIter?_eq_some {n : Nat} {s s' : CollisionState} :
    nextIter? n s = some s' → Reaches s s' := by
  intro h
  induction n generalizing s s' with
  | zero =>
    have hs : s = s' := by
      simpa using h
    subst hs
    exact Reaches.refl s
  | succ n ih =>
    cases hn : nextIter? n s with
    | none =>
      have : False := by
        have h' := h
        simp [nextIter?, hn] at h'
      exact False.elim this
    | some mid =>
      have hmid : Reaches s mid := ih hn
      have hstep : stepRel mid s' := by
        -- `h` is exactly the definitional `next? mid = some s'`.
        simpa [nextIter?, hn, stepRel] using h
      exact Relation.ReflTransGen.trans hmid (Relation.ReflTransGen.single hstep)

theorem nextIter?_eq_some_of_Reaches {s s' : CollisionState} :
    Reaches s s' → ∃ n : Nat, nextIter? n s = some s' := by
  intro h
  induction h with
  | refl =>
    exact ⟨0, rfl⟩
  | tail hreach hstep ih =>
    rcases ih with ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    -- Unfold `nextIter?` one step and use `hstep : stepRel _ _`.
    simpa [nextIter?, hn, stepRel] using hstep

theorem Reaches_iff_exists_nextIter? (s s' : CollisionState) :
    Reaches s s' ↔ ∃ n : Nat, nextIter? n s = some s' := by
  constructor
  · exact nextIter?_eq_some_of_Reaches
  · rintro ⟨n, hn⟩
    exact Reaches.of_nextIter?_eq_some hn

theorem stepRel_to_tableStep {s s' : CollisionState} (h : stepRel s s') :
    UnitSquare.table.Step s.toState s'.toState := by
  classical
  unfold stepRel at h
  -- Peel open the definitional `next?` computation.
  cases hhit : nextHit? s.pos s.vel with
  | none =>
    simp [next?, hhit] at h
  | some hit =>
    rcases hit with ⟨_hk, t⟩
    by_cases ht : 0 < t
    · let q : V := s.pos + t • s.vel
      by_cases hq : q ∈ boundary
      · -- In this branch `next? s = some cs`, so `s'` must be that `cs`.
        have hEq : next? s =
            some
              { pos := q
                pos_mem := hq
                vel := reflect (UnitSquare.normal ⟨q, hq⟩) s.vel
                vel_ne_zero :=
                  reflect_ne_zero (n := UnitSquare.normal ⟨q, hq⟩) (v := s.vel) s.vel_ne_zero } := by
          simp [next?, hhit, ht, q, hq]
        have : (some
              { pos := q
                pos_mem := hq
                vel := reflect (UnitSquare.normal ⟨q, hq⟩) s.vel
                vel_ne_zero :=
                  reflect_ne_zero (n := UnitSquare.normal ⟨q, hq⟩) (v := s.vel) s.vel_ne_zero }
            : Option CollisionState) = some s' := by
          simpa [hEq] using h
        -- Rewrite `s'` to the constructed record.
        cases this
        -- Now construct the staged `Table.Step`.
        refine ⟨q, hq, ?_, rfl, rfl⟩
        -- Flight uses convexity of the unit square.
        refine ⟨t, ht, rfl, ?_⟩
        intro r hr
        have hsreg : s.pos ∈ region := boundary_subset_region s.pos_mem
        have hqreg : q ∈ region := boundary_subset_region hq
        have hseg : segment ℝ s.pos q ⊆ region :=
          segment_subset_region (p := s.pos) (q := q) hsreg hqreg
        have : r ∈ region := hseg hr
        exact Or.inl this
      · simp [next?, hhit, ht, q, hq] at h
    · simp [next?, hhit, ht] at h

end UnitSquareMap

end Billiards
end MirandaDynamics
end HeytingLean
