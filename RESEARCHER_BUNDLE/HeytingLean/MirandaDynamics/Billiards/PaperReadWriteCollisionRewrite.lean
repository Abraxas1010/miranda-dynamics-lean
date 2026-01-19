import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteCollision

/-!
# MirandaDynamics.Billiards: deterministic collision cross-section for rewrite walls `rwWallRewrite` (WS7.3)

This file adds a deterministic, corridor-local collision-space for the **symbol-change** separating
walls `rwWallRewrite k ds cur`.

It mirrors `PaperReadWriteCollision` (read-only walls), but the supporting line has a normal of the
form `(±m, 1)` where `m = rewriteSlope k ds`. This makes the vertical incoming ray `eY` transverse
(`⟪n, eY⟫ = 1`), so the hit time is always defined and explicitly computable.

This is *not* yet the full WS7.3 “no spurious collisions” / minimal-time next-collision story: it
only provides the deterministic **first collision with the chosen rewrite wall**, plus canonical
union membership / point-level uniqueness on that union.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set
open Plane
open scoped RealInnerProductSpace

namespace PaperReadWrite

/-! ## Supporting line of a rewrite wall segment -/

/-- Normal vector for the supporting line of `rwWallRewrite k ds cur`. -/
noncomputable def rwWallRewriteNormal (k : ℤ) (ds : List Bool) (cur : Bool) : V :=
  let m := rewriteSlope k ds
  if cur then (-m) • eX + eY else m • eX + eY

/-- The affine-line constant `c` such that `⟪rwWallRewriteNormal, p⟫ = c` for points on the supporting line. -/
noncomputable def rwWallRewriteConst (k : ℤ) (ds : List Bool) (cur : Bool) : ℝ :=
  let m := rewriteSlope k ds
  if cur then 2 - m * rwBlockCenter k ds else 2 + m * rwBlockCenter k ds

/-- Supporting line of `rwWallRewrite k ds cur` (ignoring the `x`-interval restriction). -/
def rwWallRewriteLine (k : ℤ) (ds : List Bool) (cur : Bool) : Set V :=
  Line (rwWallRewriteNormal k ds cur) (rwWallRewriteConst k ds cur)

theorem rwWallRewrite_subset_rwWallRewriteLine (k : ℤ) (ds : List Bool) (cur : Bool) :
    rwWallRewrite k ds cur ⊆ rwWallRewriteLine k ds cur := by
  intro p hp
  rcases hp with ⟨_hx, hy⟩
  have hm : rewriteSlope k ds = (rewriteSlope k ds) := rfl
  cases hcur : cur
  · -- `cur=false`: `y = 2 + m*(center - x)`, so `m*x + y = 2 + m*center`.
    have : inner ℝ (rwWallRewriteNormal k ds false) p = rwWallRewriteConst k ds false := by
      -- Expand in coordinates.
      simp [rwWallRewriteNormal, rwWallRewriteConst, rwWallRewrite, rewriteSlope, hcur, hm, hy, Line,
        Plane.eX, Plane.eY, Plane.x, Plane.y, EuclideanSpace.inner_eq_sum_mul, Fin.sum_univ_two]
      ring_nf
    simpa [rwWallRewriteLine, Line] using this
  · -- `cur=true`: `y = 2 + m*(x - center)`, so `-m*x + y = 2 - m*center`.
    have : inner ℝ (rwWallRewriteNormal k ds true) p = rwWallRewriteConst k ds true := by
      simp [rwWallRewriteNormal, rwWallRewriteConst, rwWallRewrite, rewriteSlope, hcur, hm, hy, Line,
        Plane.eX, Plane.eY, Plane.x, Plane.y, EuclideanSpace.inner_eq_sum_mul, Fin.sum_univ_two]
      ring_nf
    simpa [rwWallRewriteLine, Line] using this

/-! ## A vertical cross-section and deterministic collision with a specified rewrite wall -/

namespace RewriteCollision

/-- Cross-section state: a vertical incoming ray under a *specified* rewrite wall segment. -/
structure State where
  k : ℤ
  ds : List Bool
  cur : Bool
  x0 : ℝ
  hx0 : x0 ∈ rwBlockInterval k ds

def pos (s : State) : V := Plane.mk s.x0 0
def vel (_s : State) : V := eY

/-- “Good” states: strictly inside the wall’s `x`-interval (excludes endpoint hits). -/
def Good (s : State) : Prop :=
  s.x0 ∈ Set.Ioo (rwBlockLeft s.k s.ds) (rwBlockLeft s.k s.ds + rwBlockLen s.k s.ds)

theorem Good.hx0 (s : State) (h : Good s) : s.x0 ∈ rwBlockInterval s.k s.ds := by
  exact ⟨le_of_lt h.1, le_of_lt h.2⟩

theorem inner_rwWallRewriteNormal_vel (s : State) :
    inner ℝ (rwWallRewriteNormal s.k s.ds s.cur) (vel s) = (1 : ℝ) := by
  -- `rwWallRewriteNormal = (±m)eX + eY` and `⟪eX,eY⟫=0`, `⟪eY,eY⟫=1`.
  classical
  have : inner ℝ eX eY = (0 : ℝ) := by
    simp [Plane.eX, Plane.eY, EuclideanSpace.inner_eq_sum_mul, Fin.sum_univ_two]
  cases hcur : s.cur <;>
    simp [rwWallRewriteNormal, vel, hcur, Plane.eX, Plane.eY, EuclideanSpace.inner_eq_sum_mul, Fin.sum_univ_two]

theorem inner_rwWallRewriteNormal_vel_ne_zero (s : State) :
    inner ℝ (rwWallRewriteNormal s.k s.ds s.cur) (vel s) ≠ 0 := by
  simpa [inner_rwWallRewriteNormal_vel s] using (one_ne_zero : (1 : ℝ) ≠ 0)

noncomputable def hitTime? (s : State) : Option ℝ :=
  timeToLine? (rwWallRewriteNormal s.k s.ds s.cur) (pos s) (vel s) (rwWallRewriteConst s.k s.ds s.cur)

noncomputable def hitPoint? (s : State) : Option V :=
  Option.map (fun t => pos s + t • vel s) (hitTime? s)

theorem hitTime?_eq_some (s : State) :
    hitTime? s =
      some
        (if s.cur
         then 2 + rewriteSlope s.k s.ds * (s.x0 - rwBlockCenter s.k s.ds)
         else 2 + rewriteSlope s.k s.ds * (rwBlockCenter s.k s.ds - s.x0)) := by
  classical
  have hv : inner ℝ (rwWallRewriteNormal s.k s.ds s.cur) (vel s) ≠ 0 :=
    inner_rwWallRewriteNormal_vel_ne_zero s
  unfold hitTime? timeToLine?
  have hne : ¬inner ℝ (rwWallRewriteNormal s.k s.ds s.cur) (vel s) = 0 := hv
  -- Since `⟪n,eY⟫ = 1`, the division simplifies.
  cases hcur : s.cur <;>
    simp [hne, pos, vel, rwWallRewriteNormal, rwWallRewriteConst, hcur,
      Plane.mk, Plane.eX, Plane.eY, EuclideanSpace.inner_eq_sum_mul, Fin.sum_univ_two] <;>
    ring_nf

theorem hitPoint?_eq_some (s : State) :
    hitPoint? s =
      some
        (Plane.mk s.x0
          (if s.cur
           then 2 + rewriteSlope s.k s.ds * (s.x0 - rwBlockCenter s.k s.ds)
           else 2 + rewriteSlope s.k s.ds * (rwBlockCenter s.k s.ds - s.x0))) := by
  classical
  simp [hitPoint?, hitTime?_eq_some, pos, vel, Plane.mk, Plane.eY]

theorem hitPoint_mem_rwWallRewrite (s : State) (hx0 : s.x0 ∈ rwBlockInterval s.k s.ds) :
    Plane.mk s.x0
        (if s.cur
         then 2 + rewriteSlope s.k s.ds * (s.x0 - rwBlockCenter s.k s.ds)
         else 2 + rewriteSlope s.k s.ds * (rwBlockCenter s.k s.ds - s.x0))
      ∈ rwWallRewrite s.k s.ds s.cur := by
  cases hcur : s.cur <;>
    simp [rwWallRewrite, hx0, rwBlockCenter, Plane.mk, Plane.x, Plane.y, hcur] <;>
    ring_nf

/-- Deterministic one-step collision with the specified rewrite wall (staged, ignores other walls). -/
noncomputable def next? (s : State) : Option (V × V) :=
  match hitPoint? s with
  | none => none
  | some q =>
      some (q, reflect (rwWallRewriteNormal s.k s.ds s.cur) (vel s))

theorem next?_eq_some_of_Good (s : State) (hgood : Good s) :
    ∃ q : V,
      next? s = some (q, reflect (rwWallRewriteNormal s.k s.ds s.cur) (vel s)) ∧ q ∈ rwWallRewrite s.k s.ds s.cur := by
  have hx0 : s.x0 ∈ rwBlockInterval s.k s.ds := Good.hx0 s hgood
  refine ⟨Plane.mk s.x0
      (if s.cur
       then 2 + rewriteSlope s.k s.ds * (s.x0 - rwBlockCenter s.k s.ds)
       else 2 + rewriteSlope s.k s.ds * (rwBlockCenter s.k s.ds - s.x0)), ?_, ?_⟩
  · simp [next?, hitPoint?_eq_some]
  · exact hitPoint_mem_rwWallRewrite s hx0

/-! ### “Steeper than read-only” (minimal local fact) -/

theorem rewriteSlope_lt_one (k : ℤ) (ds : List Bool) : rewriteSlope k ds < 1 := by
  -- `rewriteSlope = 1/(1+len)` and `len>0`.
  have hlen : 0 < rwBlockLen k ds := rwBlockLen_pos k ds
  have hden : (1 : ℝ) < 1 + rwBlockLen k ds := by linarith
  -- `1/(1+len) < 1` when `1+len > 1`.
  simpa [rewriteSlope] using (one_div_lt_one (by linarith) |>.2 hden)

theorem y_reflect_rwWallRewriteNormal_eY_neg (k : ℤ) (ds : List Bool) (cur : Bool) :
    y (reflect (rwWallRewriteNormal k ds cur) eY) < 0 := by
  classical
  -- Use the explicit reflection formula and compute the `y`-coordinate.
  have hm0 : 0 ≤ rewriteSlope k ds := by
    -- `rewriteSlope = 1/(1+len)`, and `1+len > 0`.
    have hlen : 0 < rwBlockLen k ds := rwBlockLen_pos k ds
    have : 0 < (1 : ℝ) + rwBlockLen k ds := by linarith
    have : 0 < rewriteSlope k ds := by
      simp [rewriteSlope, one_div, inv_pos.2 this]
    exact le_of_lt this
  have hm1 : rewriteSlope k ds < 1 := rewriteSlope_lt_one k ds
  -- Compute `y` after reflection: it is `(m^2 - 1)/(m^2 + 1)`.
  have hnormsq :
      ((‖rwWallRewriteNormal k ds cur‖ : ℝ) ^ 2) = (rewriteSlope k ds) ^ 2 + 1 := by
    -- Norm square is the inner product with itself.
    have :
        ((‖rwWallRewriteNormal k ds cur‖ : ℝ) ^ 2) =
          inner ℝ (rwWallRewriteNormal k ds cur) (rwWallRewriteNormal k ds cur) := by
      simpa using (real_inner_self_eq_norm_sq (x := rwWallRewriteNormal k ds cur)).symm
    -- `rwWallRewriteNormal = (±m)eX + eY` so `⟪n,n⟫ = m^2 + 1`.
    cases cur <;>
      simp [this, rwWallRewriteNormal, Plane.eX, Plane.eY, EuclideanSpace.inner_eq_sum_mul, Fin.sum_univ_two]
  have hy :
      y (reflect (rwWallRewriteNormal k ds cur) eY) =
        ((rewriteSlope k ds) ^ 2 - 1) / ((rewriteSlope k ds) ^ 2 + 1) := by
    -- From `reflect_apply` with `⟪n,eY⟫ = 1` and `y n = 1`.
    have hin : inner ℝ (rwWallRewriteNormal k ds cur) eY = (1 : ℝ) := by
      -- same computation as `inner_rwWallRewriteNormal_vel`.
      cases cur <;>
        simp [rwWallRewriteNormal, Plane.eX, Plane.eY, EuclideanSpace.inner_eq_sum_mul, Fin.sum_univ_two]
    have hyn : y (rwWallRewriteNormal k ds cur) = 1 := by
      cases cur <;> simp [rwWallRewriteNormal, Plane.y, Plane.eX, Plane.eY]
    -- Evaluate the `y` coordinate of `reflect_apply`.
    simp [reflect_apply, hin, hnormsq, hyn, Plane.y, Plane.eX, Plane.eY, div_eq_mul_inv]
    ring_nf
  -- Show the RHS is negative.
  have hdenpos : 0 < (rewriteSlope k ds) ^ 2 + 1 := by positivity
  have hnumneg : (rewriteSlope k ds) ^ 2 - 1 < 0 := by
    have : (rewriteSlope k ds) ^ 2 < 1 := by
      -- square preserves strict inequality for `0 ≤ m < 1`.
      have := sq_lt_sq.2 (And.intro hm1 (by linarith [hm0]))
      simpa [one_pow] using this
    linarith
  -- Divide by positive denominator.
  have : ((rewriteSlope k ds) ^ 2 - 1) / ((rewriteSlope k ds) ^ 2 + 1) < 0 := by
    exact (div_neg_iff).2 ⟨hnumneg, hdenpos⟩
  simpa [hy] using this

end RewriteCollision

/-! ## Canonical rewrite collision states (Appendix indexing) -/

namespace RewriteCollisionCanonical

open RewriteCollision

structure State where
  k : ℤ
  pref : List Bool
  cur : Bool
  hlen : pref.length = indexNat k
  x0 : ℝ
  hx0 : x0 ∈ rwBlockInterval k (pref ++ [cur])

def ds (s : State) : List Bool := s.pref ++ [s.cur]

def toNoncanonical (s : State) : RewriteCollision.State :=
  { k := s.k, ds := s.ds, cur := s.cur, x0 := s.x0, hx0 := by simpa [ds] using s.hx0 }

/-- Good states exclude endpoint hits inside the block interval. -/
def Good (s : State) : Prop :=
  s.x0 ∈ Set.Ioo (rwBlockLeft s.k s.ds) (rwBlockLeft s.k s.ds + rwBlockLen s.k s.ds)

theorem Good.toNoncanonical (s : State) (h : Good s) : RewriteCollision.Good (toNoncanonical s) := by
  simpa [RewriteCollision.Good, toNoncanonical, ds] using h

noncomputable def next? (s : State) : Option (V × V) :=
  RewriteCollision.next? (toNoncanonical s)

theorem next?_eq_some_of_Good (s : State) (hgood : Good s) :
    ∃ q : V,
      next? s = some (q, reflect (rwWallRewriteNormal s.k s.ds s.cur) eY) ∧ q ∈ rwWallRewrite s.k s.ds s.cur := by
  have hgood' : RewriteCollision.Good (toNoncanonical s) := Good.toNoncanonical s hgood
  simpa [next?, toNoncanonical, RewriteCollision.vel] using RewriteCollision.next?_eq_some_of_Good (s := toNoncanonical s) hgood'

theorem next?_hit_mem_rwWallRewriteUnionCanonical (s : State) (hgood : Good s) :
    ∃ q : V, q ∈ rwWallRewriteUnionCanonical ∧ next? s = some (q, reflect (rwWallRewriteNormal s.k s.ds s.cur) eY) := by
  rcases next?_eq_some_of_Good s hgood with ⟨q, hnext, hq⟩
  refine ⟨q, ?_, hnext⟩
  refine ⟨s.k, s.pref, s.cur, s.hlen, ?_⟩
  simpa [rwWallRewriteUnionCanonical, PaperReadWriteBoundary.rwDigits, ds] using hq

/-- Point-level uniqueness on the canonical rewrite-wall union: `x`-domain disjointness identifies the block. -/
theorem rwWallRewriteUnionCanonical_unique_of_hit (s : State) {q : V}
    (hq : q ∈ rwWallRewrite s.k s.ds s.cur) (hq' : q ∈ rwWallRewriteUnionCanonical) :
    ∃ pref' cur', pref' = s.pref ∧ cur' = s.cur := by
  rcases hq' with ⟨k', pref', cur', hk', hq'wall⟩
  have hx : x q ∈ rwBlockInterval s.k s.ds := hq.1
  have hx' : x q ∈ rwBlockInterval k' (pref' ++ [cur']) := hq'wall.1
  have hEq :
      s.pref ++ [s.cur] = pref' ++ [cur'] := by
    exact
      PaperReadWrite.rwBlockInterval_eq_of_mem_of_rwDigits (k := s.k)
        (pref := s.pref) (pref' := pref') (cur := s.cur) (cur' := cur')
        (hL := s.hlen) (hL' := hk') (hx := by simpa [ds] using hx) (hx' := hx')
  refine ⟨pref', cur', ?_, ?_⟩
  · have : pref' = s.pref := by
      have ht := congrArg (fun l => l.take s.pref.length) hEq.symm
      simpa [List.take_append_of_le_length, s.hlen, ds] using ht
    exact this.symm
  · have : cur' = s.cur := by
      have hn : (s.pref ++ [s.cur]).getLast? = some s.cur := by simp
      have hn' : (pref' ++ [cur']).getLast? = some cur' := by simp
      have : some cur' = some s.cur := by
        simpa [hEq] using (hn'.trans hn.symm)
      simpa using Option.some.inj this
    exact this.symm

end RewriteCollisionCanonical

end PaperReadWrite

end Billiards
end MirandaDynamics
end HeytingLean

