import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteWalls
import HeytingLean.MirandaDynamics.Billiards.LineCollision
import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteBoundary
import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteNoSpurious

/-!
# MirandaDynamics.Billiards: deterministic ray→wall collision for Appendix read-only walls

This file is the first mechanizable step toward the WS7.3 geometry gap:

* take the Appendix read-only separating walls `rwWall k ds cur` (straight segments of slope `±1`);
* define a small **collision-space cross-section** consisting of vertical incoming rays under a
  specified wall segment;
* implement a deterministic one-step `next?` that computes the unique collision with that wall
  and reflects the velocity specularly.

Crucially, this does **not** yet define the full billiard table boundary (union over all walls and
parabolic shift arcs), nor does it prove “no spurious collisions” with *other* walls. Those are
the long-horizon WS7.3 tasks.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set
open scoped RealInnerProductSpace

namespace Plane

def mk (x y : ℝ) : V :=
  fun i => Fin.cases x (fun _ => y) i

@[simp] theorem mk_x (x y : ℝ) : x (mk x y) = x := by
  simp [mk, x]

@[simp] theorem mk_y (x y : ℝ) : y (mk x y) = y := by
  simp [mk, y]

end Plane

open Plane

/-! ## Supporting line of a read-only wall segment -/

/-- The affine-line constant `c` for the Appendix wall with normal `rwWallNormal cur`. -/
noncomputable def rwWallConst (k : ℤ) (ds : List Bool) (cur : Bool) : ℝ :=
  if cur then rwBlockCenter k ds - 2 else rwBlockCenter k ds + 2

/-- The supporting affine line of `rwWall k ds cur` (ignoring the `x`-interval restriction). -/
def rwWallLine (k : ℤ) (ds : List Bool) (cur : Bool) : Set V :=
  Line (rwWallNormal cur) (rwWallConst k ds cur)

theorem mem_rwWallLine_iff (k : ℤ) (ds : List Bool) (cur : Bool) (p : V) :
    p ∈ rwWallLine k ds cur ↔ inner ℝ (rwWallNormal cur) p = rwWallConst k ds cur := Iff.rfl

theorem rwWall_subset_rwWallLine (k : ℤ) (ds : List Bool) (cur : Bool) :
    rwWall k ds cur ⊆ rwWallLine k ds cur := by
  intro p hp
  rcases hp with ⟨hx, hy⟩
  cases cur <;> simp [rwWall, rwWallLine, rwWallConst, rwWallNormal] at hx hy ⊢
  · -- `cur = false`: `y = 2 + (center - x)` so `x + y = 2 + center`.
    have : x p + y p = 2 + rwBlockCenter k ds := by
      linarith
    -- Unfold the normal `eX + eY` as coordinates.
    -- `simp` turns `inner` into the dot product over the two coordinates.
    simpa [rwWallNormal, Plane.eX, Plane.eY, Plane.x, Plane.y, EuclideanSpace.inner_eq_sum_mul,
      Fin.sum_univ_two, this]
  · -- `cur = true`: `y = 2 + (-center + x)` so `x - y = center - 2`.
    have : x p - y p = rwBlockCenter k ds - 2 := by
      linarith
    simpa [rwWallNormal, Plane.eX, Plane.eY, Plane.x, Plane.y, EuclideanSpace.inner_eq_sum_mul,
      Fin.sum_univ_two, this]

/-! ## A simple cross-section and deterministic next collision with a specified wall -/

namespace ReadOnlyCollision

/-- Cross-section state: a vertical incoming ray under a *specified* wall segment. -/
structure State where
  k : ℤ
  ds : List Bool
  cur : Bool
  x0 : ℝ
  hx0 : x0 ∈ rwBlockInterval k ds

/-- The ambient starting point on the cross-section line `y=0`. -/
def pos (s : State) : V :=
  mk s.x0 0

/-- The incoming velocity (vertical upward). -/
def vel (_s : State) : V :=
  eY

/-- “Good” states: strictly inside the wall’s `x`-interval (excludes endpoint hits). -/
def Good (s : State) : Prop :=
  s.x0 ∈ Set.Ioo (rwBlockLeft s.k s.ds) (rwBlockLeft s.k s.ds + rwBlockLen s.k s.ds)

theorem Good.hx0 (s : State) (h : Good s) : s.x0 ∈ rwBlockInterval s.k s.ds := by
  exact ⟨le_of_lt h.1, le_of_lt h.2⟩

theorem inner_rwWallNormal_vel_ne_zero (s : State) :
    inner ℝ (rwWallNormal s.cur) (vel s) ≠ 0 := by
  cases s.cur <;> simp [vel, rwWallNormal, Plane.eX, Plane.eY, EuclideanSpace.inner_eq_sum_mul, Fin.sum_univ_two]

theorem inner_rwWallNormal_eY (cur : Bool) :
    inner ℝ (rwWallNormal cur) eY = (if cur then (-1 : ℝ) else (1 : ℝ)) := by
  cases cur <;> simp [rwWallNormal, Plane.eX, Plane.eY, EuclideanSpace.inner_eq_sum_mul, Fin.sum_univ_two]

theorem norm_rwWallNormal_sq (cur : Bool) :
    ((‖rwWallNormal cur‖ : ℝ) ^ 2) = (2 : ℝ) := by
  -- Rewrite the norm-square as an inner product and compute in coordinates.
  have :
      ((‖rwWallNormal cur‖ : ℝ) ^ 2) =
        inner ℝ (rwWallNormal cur) (rwWallNormal cur) := by
    simpa using (real_inner_self_eq_norm_sq (x := rwWallNormal cur)).symm
  -- Now evaluate the inner product of `eX ± eY` with itself.
  cases cur <;> simp [this, rwWallNormal, Plane.eX, Plane.eY, EuclideanSpace.inner_eq_sum_mul, Fin.sum_univ_two]

theorem reflect_rwWallNormal_eY (cur : Bool) :
    reflect (rwWallNormal cur) eY = (if cur then eX else -eX) := by
  cases cur <;> simp [rwWallNormal, reflect_apply, inner_rwWallNormal_eY, norm_rwWallNormal_sq,
    Plane.eX, Plane.eY, EuclideanSpace.inner_eq_sum_mul, Fin.sum_univ_two]

noncomputable def hitTime? (s : State) : Option ℝ :=
  timeToLine? (rwWallNormal s.cur) (pos s) (vel s) (rwWallConst s.k s.ds s.cur)

noncomputable def hitPoint? (s : State) : Option V :=
  Option.map (fun t => pos s + t • vel s) (hitTime? s)

theorem hitTime?_eq_some (s : State) :
    hitTime? s =
      some
        (if s.cur then s.x0 + 2 - rwBlockCenter s.k s.ds else 2 + rwBlockCenter s.k s.ds - s.x0) := by
  classical
  have hv : inner ℝ (rwWallNormal s.cur) (vel s) ≠ 0 :=
    inner_rwWallNormal_vel_ne_zero s
  unfold hitTime? timeToLine?
  have hne : ¬inner ℝ (rwWallNormal s.cur) (vel s) = 0 := hv
  simp [hne, rwWallConst, pos, vel, EuclideanSpace.inner_eq_sum_mul, Plane.mk, Plane.eX, Plane.eY, Fin.sum_univ_two,
    rwWallNormal, Plane.x, Plane.y]
  -- `simp` reduces to a `ring` identity.
  ring_nf

theorem hitPoint?_eq_some (s : State) :
    hitPoint? s =
      some
        (mk s.x0
          (if s.cur then s.x0 + 2 - rwBlockCenter s.k s.ds else 2 + rwBlockCenter s.k s.ds - s.x0)) := by
  classical
  -- Unfold and use `hitTime?_eq_some`.
  simp [hitPoint?, hitTime?_eq_some, pos, vel, Plane.mk, Plane.eY]

theorem hitPoint_mem_rwWall (s : State) (hx0 : s.x0 ∈ rwBlockInterval s.k s.ds) :
    mk s.x0 (if s.cur then s.x0 + 2 - rwBlockCenter s.k s.ds else 2 + rwBlockCenter s.k s.ds - s.x0) ∈
      rwWall s.k s.ds s.cur := by
  -- By construction, `x` is in the interval and `y` satisfies the wall equation.
  cases s.cur <;> simp [rwWall, hx0, rwBlockCenter, rwBlockLeft, rwBlockLen, Plane.mk, Plane.x, Plane.y]

/-- Deterministic one-step collision with the specified read-only wall. -/
noncomputable def next? (s : State) : Option (V × V) :=
  match hitPoint? s with
  | none => none
  | some q =>
      some (q, reflect (rwWallNormal s.cur) (vel s))

theorem next?_eq_some_of_Good (s : State) (hgood : Good s) :
    ∃ q : V, next? s = some (q, reflect (rwWallNormal s.cur) (vel s)) ∧ q ∈ rwWall s.k s.ds s.cur := by
  have hx0 : s.x0 ∈ rwBlockInterval s.k s.ds := Good.hx0 s hgood
  refine ⟨mk s.x0
      (if s.cur then s.x0 + 2 - rwBlockCenter s.k s.ds else 2 + rwBlockCenter s.k s.ds - s.x0), ?_, ?_⟩
  · simp [next?, hitPoint?_eq_some]
  · exact hitPoint_mem_rwWall s hx0

/-! ## The redirecting wall `tildeWall` (Appendix: read-only gadget) -/

theorem tildeWall_subset_rwWallLine (k : ℤ) (ds : List Bool) (cur : Bool) :
    tildeWall k ds cur ⊆ Line (rwWallNormal cur) (rwBlockCenter k ds) := by
  intro p hp
  rcases hp with ⟨_hx, hy⟩
  cases cur <;> simp [tildeWall, rwWallNormal, shift] at hy ⊢
  · -- `cur=false`: `y = rwBlockCenter - x`, so `x + y = rwBlockCenter`.
    have : x p + y p = rwBlockCenter k ds := by linarith
    simpa [Plane.eX, Plane.eY, Plane.x, Plane.y, EuclideanSpace.inner_eq_sum_mul, Fin.sum_univ_two, this]
  · -- `cur=true`: `y = x - rwBlockCenter`, so `x - y = rwBlockCenter`.
    have : x p - y p = rwBlockCenter k ds := by linarith
    simpa [Plane.eX, Plane.eY, Plane.x, Plane.y, EuclideanSpace.inner_eq_sum_mul, Fin.sum_univ_two, this]

/-- Two-bounce read-only step: collide with `rwWall`, then with `tildeWall`, returning to vertical velocity. -/
noncomputable def next2? (s : State) : Option (V × V) := by
  classical
  -- First collision.
  rcases next? s with
  | none => exact none
  | some out1 =>
      let q₁ : V := out1.1
      let v₁ : V := out1.2
      -- Second collision: compute time to the supporting line of `tildeWall`.
      let t₂? := timeToLine? (rwWallNormal s.cur) q₁ v₁ (rwBlockCenter s.k s.ds)
      match t₂? with
      | none => exact none
      | some t₂ =>
          let q₂ := q₁ + t₂ • v₁
          exact some (q₂, reflect (rwWallNormal s.cur) v₁)

theorem next2?_eq_some_of_Good (s : State) (hgood : Good s) :
    ∃ q₂ : V, ∃ q₁ : V,
      next2? s = some (q₂, eY) ∧
      q₁ ∈ rwWall s.k s.ds s.cur ∧
      q₂ ∈ tildeWall s.k s.ds s.cur ∧
      x q₂ = s.x0 + shift s.cur := by
  classical
  rcases next?_eq_some_of_Good s hgood with ⟨q₁, hnext1, hq₁⟩
  have hv₁ :
      reflect (rwWallNormal s.cur) (vel s) =
        (if s.cur then eX else -eX) := by
    simpa [vel] using (reflect_rwWallNormal_eY (cur := s.cur))
  -- Compute `q₁` explicitly from the first-collision formula.
  have hq₁' :
      q₁ =
        mk s.x0 (if s.cur then s.x0 + 2 - rwBlockCenter s.k s.ds else 2 + rwBlockCenter s.k s.ds - s.x0) := by
    -- `next?` uses `hitPoint?`, so `hnext1` pins down the first collision point.
    simpa [next?, hitPoint?_eq_some] using congrArg Prod.fst (Option.some.inj hnext1)
  -- Set up the second collision data.
  have hline₁ : q₁ ∈ Line (rwWallNormal s.cur) (rwWallConst s.k s.ds s.cur) :=
    (rwWall_subset_rwWallLine s.k s.ds s.cur) hq₁
  have hnv₁ : inner ℝ (rwWallNormal s.cur) (reflect (rwWallNormal s.cur) (vel s)) ≠ 0 := by
    -- From the explicit value `±eX`.
    cases s.cur <;> simp [hv₁, rwWallNormal, Plane.eX, Plane.eY, EuclideanSpace.inner_eq_sum_mul, Fin.sum_univ_two]
  -- The second hit time is exactly `2`.
  have ht₂ :
      timeToLine? (rwWallNormal s.cur) q₁ (reflect (rwWallNormal s.cur) (vel s)) (rwBlockCenter s.k s.ds) =
        some (2 : ℝ) := by
    -- Solve the line equation using inner products and the fact `q₁` is on the first line.
    have hinner_q₁ :
        inner ℝ (rwWallNormal s.cur) q₁ = rwWallConst s.k s.ds s.cur := by
      exact hline₁
    -- Evaluate the time-to-line formula.
    unfold timeToLine?
    have hne : ¬inner ℝ (rwWallNormal s.cur) (reflect (rwWallNormal s.cur) (vel s)) = 0 := hnv₁
    simp [hne, hinner_q₁, rwWallConst, hv₁, vel, rwWallNormal, shift, Plane.eX, Plane.eY,
      EuclideanSpace.inner_eq_sum_mul, Fin.sum_univ_two]
  -- Compute the second collision point.
  refine ⟨q₁ + (2 : ℝ) • (reflect (rwWallNormal s.cur) (vel s)), q₁, ?_, hq₁, ?_, ?_⟩
  · -- Expand `next2?` and use the computed `t₂`.
    simp [next2?, hnext1, ht₂, vel, reflect_reflect]
  · -- Membership in `tildeWall`.
    -- Use the explicit coordinate computations for `q₁` and the velocity `±eX`.
    subst hq₁'
    cases s.cur <;> simp [tildeWall, shift, hv₁, Plane.mk, Plane.x, Plane.y, rwBlockInterval, rwBlockLeft, rwBlockLen]
      -- `simp` leaves linear arithmetic side-goals for interval membership.
      <;> try
        (constructor <;> linarith)
  · -- `x`-coordinate of `q₂` is shifted by `±2`.
    subst hq₁'
    cases s.cur <;> simp [shift, hv₁, Plane.mk, Plane.x, Plane.y]

theorem next2?_encode_x (s : State) (hgood : Good s) :
    Option.map (fun out : V × V => x out.1) (next2? s) = some (s.x0 + shift s.cur) := by
  rcases next2?_eq_some_of_Good s hgood with ⟨q₂, _q₁, hnext2, _hq₁, _hq₂, hx⟩
  simp [hnext2, hx]

/-! ## Collision uniqueness for a fixed wall line (no global “no other walls” yet) -/

theorem hitTime_unique {n p v : V} {c t₁ t₂ : ℝ}
    (hnv : inner ℝ n v ≠ 0)
    (h₁ : p + t₁ • v ∈ Line n c) (h₂ : p + t₂ • v ∈ Line n c) :
    t₁ = t₂ := by
  have hline₁ : inner ℝ n (p + t₁ • v) = c := h₁
  have hline₂ : inner ℝ n (p + t₂ • v) = c := h₂
  -- Expand and subtract the two equations.
  have :
      inner ℝ n p + t₁ * inner ℝ n v = inner ℝ n p + t₂ * inner ℝ n v := by
    simpa [inner_add_smul] using congrArg id (hline₁.trans hline₂.symm)
  -- Cancel and divide by the nonzero factor.
  have : (t₁ - t₂) * inner ℝ n v = 0 := by
    nlinarith
  have ht : t₁ - t₂ = 0 := by
    exact mul_eq_zero.mp this |>.resolve_right hnv
  linarith

end ReadOnlyCollision

/-! ## Canonical read-only collision states (indexed as in the Appendix unions) -/

namespace ReadOnlyCollisionCanonical

open PaperReadWrite

/-- Canonical cross-section state: uses the Appendix indexing `pref.length = indexNat k`. -/
structure State where
  k : ℤ
  pref : List Bool
  cur : Bool
  hlen : pref.length = indexNat k
  x0 : ℝ
  hx0 : x0 ∈ rwBlockInterval k (pref ++ [cur])

def ds (s : State) : List Bool := s.pref ++ [s.cur]

@[simp] theorem ds_length (s : State) : s.ds.length = indexNat s.k + 1 := by
  simp [ds, s.hlen, List.length_append]

def pos (s : State) : V := Plane.mk s.x0 0
def vel (_s : State) : V := eY

/-- Good states exclude endpoint hits inside the block interval. -/
def Good (s : State) : Prop :=
  s.x0 ∈ Set.Ioo (rwBlockLeft s.k s.ds) (rwBlockLeft s.k s.ds + rwBlockLen s.k s.ds)

theorem Good.hx0 (s : State) (h : Good s) : s.x0 ∈ rwBlockInterval s.k s.ds := by
  exact ⟨le_of_lt h.1, le_of_lt h.2⟩

noncomputable def rwWallConst (s : State) : ℝ :=
  if s.cur then rwBlockCenter s.k s.ds - 2 else rwBlockCenter s.k s.ds + 2

noncomputable def hitTime? (s : State) : Option ℝ :=
  timeToLine? (rwWallNormal s.cur) (pos s) (vel s) (rwWallConst s)

noncomputable def hitPoint? (s : State) : Option V :=
  Option.map (fun t => pos s + t • vel s) (hitTime? s)

theorem hitTime?_eq_some (s : State) :
    hitTime? s =
      some
        (if s.cur then s.x0 + 2 - rwBlockCenter s.k s.ds else 2 + rwBlockCenter s.k s.ds - s.x0) := by
  classical
  have hv : inner ℝ (rwWallNormal s.cur) (vel s) ≠ 0 := by
    -- Same computation as `ReadOnlyCollision.inner_rwWallNormal_vel_ne_zero`.
    cases s.cur <;> simp [vel, rwWallNormal, Plane.eX, Plane.eY, EuclideanSpace.inner_eq_sum_mul, Fin.sum_univ_two]
  unfold hitTime? timeToLine?
  have hne : ¬inner ℝ (rwWallNormal s.cur) (vel s) = 0 := hv
  simp [hne, rwWallConst, pos, vel, EuclideanSpace.inner_eq_sum_mul, Plane.mk, Plane.eX, Plane.eY, Fin.sum_univ_two,
    rwWallNormal, Plane.x, Plane.y]
  ring_nf

theorem hitPoint?_eq_some (s : State) :
    hitPoint? s =
      some
        (Plane.mk s.x0
          (if s.cur then s.x0 + 2 - rwBlockCenter s.k s.ds else 2 + rwBlockCenter s.k s.ds - s.x0)) := by
  classical
  simp [hitPoint?, hitTime?_eq_some, pos, vel, Plane.mk, Plane.eY]

theorem hitPoint_mem_rwWall (s : State) (hx0 : s.x0 ∈ rwBlockInterval s.k s.ds) :
    Plane.mk s.x0
        (if s.cur then s.x0 + 2 - rwBlockCenter s.k s.ds else 2 + rwBlockCenter s.k s.ds - s.x0)
      ∈ rwWall s.k s.ds s.cur := by
  cases s.cur <;> simp [rwWall, hx0, rwBlockCenter, rwBlockLeft, rwBlockLen, Plane.mk, Plane.x, Plane.y]

/-- Deterministic one-step collision with the canonical read-only wall. -/
noncomputable def next? (s : State) : Option (V × V) :=
  match hitPoint? s with
  | none => none
  | some q =>
      some (q, reflect (rwWallNormal s.cur) (vel s))

theorem next?_eq_some_of_Good (s : State) (hgood : Good s) :
    ∃ q : V, next? s = some (q, reflect (rwWallNormal s.cur) (vel s)) ∧ q ∈ rwWall s.k s.ds s.cur := by
  have hx0 : s.x0 ∈ rwBlockInterval s.k s.ds := Good.hx0 s hgood
  refine ⟨Plane.mk s.x0
      (if s.cur then s.x0 + 2 - rwBlockCenter s.k s.ds else 2 + rwBlockCenter s.k s.ds - s.x0), ?_, ?_⟩
  · simp [next?, hitPoint?_eq_some]
  · exact hitPoint_mem_rwWall s hx0

/-- The first hit is always on the canonical read-only wall union. -/
theorem next?_hit_mem_rwWallUnionCanonical (s : State) (hgood : Good s) :
    ∃ q : V, q ∈ rwWallUnionCanonical ∧ next? s = some (q, reflect (rwWallNormal s.cur) (vel s)) := by
  rcases next?_eq_some_of_Good s hgood with ⟨q, hnext, hq⟩
  refine ⟨q, ?_, hnext⟩
  refine ⟨s.k, s.pref, s.cur, s.hlen, ?_⟩
  simpa [rwWallUnionCanonical, PaperReadWriteBoundary.rwDigits, ds, State.ds] using hq

/-- “No spurious first collisions”: a vertical incoming ray at `x0` cannot hit a *different* canonical
read-only wall, because the `x`-domains are disjoint. -/
theorem rwWallUnionCanonical_unique_of_hit (s : State) {q : V}
    (hq : q ∈ rwWall s.k s.ds s.cur) (hq' : q ∈ rwWallUnionCanonical) :
    ∃ pref' cur', pref' = s.pref ∧ cur' = s.cur := by
  rcases hq' with ⟨k', pref', cur', hk', hq'wall⟩
  -- The collision point has x-coordinate `x0`.
  have hx : x q ∈ rwBlockInterval s.k s.ds := hq.1
  have hx' : x q ∈ rwBlockInterval k' (pref' ++ [cur']) := hq'wall.1
  -- `rwBlockInterval` membership forces the digit-list to be the same (under the canonical lengths).
  have hEq :
      s.pref ++ [s.cur] = pref' ++ [cur'] := by
    -- Ensure the length hypotheses match the canonical union.
    have hkLen : (s.pref).length = indexNat s.k := s.hlen
    exact
      PaperReadWrite.rwBlockInterval_eq_of_mem_of_rwDigits (k := s.k)
        (pref := s.pref) (pref' := pref') (cur := s.cur) (cur' := cur')
        (hL := hkLen)
        (hL' := hk')
        (hx := by simpa [State.ds, ds] using hx)
        (hx' := hx')
  -- Conclude `pref' = pref` and `cur' = cur`.
  refine ⟨pref', cur', ?_, ?_⟩
  · -- extract prefixes by comparing list lengths
    have : pref' = s.pref := by
      -- `pref ++ [cur]` equality implies prefix equality.
      -- Use `List.append_right_cancel` after rewriting as `pref ++ [cur]`.
      have := congrArg (fun l => l.take (s.pref.length)) hEq.symm
      -- simplify `take` on `pref ++ [cur]`.
      simpa [List.take_append_of_le_length, s.hlen] using this
    exact this.symm
  · -- last digit equality
    have : cur' = s.cur := by
      -- compare `getLast` (safe since lists are nonempty)
      have hn : (s.pref ++ [s.cur]).getLast? = some s.cur := by
        simp
      have hn' : (pref' ++ [cur']).getLast? = some cur' := by
        simp
      -- rewrite with `hEq`
      have : some cur' = some s.cur := by
        simpa [hEq] using (hn'.trans hn.symm)
      simpa using Option.some.inj this
    exact this.symm

end ReadOnlyCollisionCanonical

end Billiards
end MirandaDynamics
end HeytingLean
