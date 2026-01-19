import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteBoundary
import Mathlib.Topology.Algebra.Field

/-!
# MirandaDynamics.Billiards: “no spurious collisions” scaffolding for read–write walls (WS7.3)

The Appendix of Miranda–Ramos (arXiv:2512.19156) rules out unintended collisions between the many
read–write gadget wall segments by explicit separation estimates.

This file provides the *first mechanizable layer* needed for such arguments:

1) express each `rwBlockInterval k ds` as the image of the Cantor cylinder interval under the affine
   embedding `tau k`;
2) transfer disjointness of Cantor cylinders (fixed digit prefixes) to disjointness of the
   corresponding wall `x`-domains on the table.

These lemmas are a prerequisite for any deterministic “next collision” construction over the wall
union, because they reduce “could we hit another wall?” to interval-disjointness on the `x`
coordinate.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set

namespace PaperReadWrite

/-- The affine offset in `tau k x = headScale k * x + tauOffset k`. -/
noncomputable def tauOffset (k : ℤ) : ℝ :=
  if k < 0 then headScale k else 1 - 2 * headScale k

theorem tau_eq_affine (k : ℤ) (x : ℝ) : tau k x = headScale k * x + tauOffset k := by
  by_cases hk : k < 0
  · simp [tau, tauOffset, hk]
    ring_nf
  · simp [tau, tauOffset, hk]
    ring_nf

theorem tau_sub (k : ℤ) (x y : ℝ) : tau k x - tau k y = headScale k * (x - y) := by
  -- `tau k` is affine with slope `headScale k`, so differences scale.
  simp [tau_eq_affine, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul, mul_assoc,
    mul_left_comm, mul_comm]

theorem rwBlockLeft_separated_of_length_eq (k : ℤ) {ds ds' : List Bool} (hlen : ds.length = ds'.length)
    (hne : ds ≠ ds') :
    |rwBlockLeft k ds - rwBlockLeft k ds'| ≥ 2 * rwBlockLen k ds := by
  -- Reduce to separation of Cantor cylinder left endpoints, then scale by `headScale k`.
  have hs : 0 ≤ headScale k := le_of_lt (headScale_pos k)
  have hsep : |cantorLeft ds - cantorLeft ds'| ≥ 2 * cantorWidth ds :=
    cantorLeft_separated_of_length_eq (ds := ds) (ds' := ds') hlen hne
  -- Rewrite `rwBlockLeft` and `rwBlockLen` and use `tau_sub`.
  have :
      |rwBlockLeft k ds - rwBlockLeft k ds'| =
        headScale k * |cantorLeft ds - cantorLeft ds'| := by
    -- `rwBlockLeft k ds = tau k (cantorLeft ds)` and `abs (a*b) = a*abs b` for `a ≥ 0`.
    simp [rwBlockLeft, tau_sub, abs_mul, abs_of_nonneg hs, mul_assoc, mul_left_comm, mul_comm]
  -- Multiply the separation inequality by the (nonnegative) scale.
  have hscaled : headScale k * |cantorLeft ds - cantorLeft ds'| ≥ headScale k * (2 * cantorWidth ds) := by
    exact mul_le_mul_of_nonneg_left hsep hs
  -- Finish by rewriting.
  calc
    |rwBlockLeft k ds - rwBlockLeft k ds'|
        = headScale k * |cantorLeft ds - cantorLeft ds'| := this
    _ ≥ headScale k * (2 * cantorWidth ds) := hscaled
    _ = 2 * rwBlockLen k ds := by
          simp [rwBlockLen, mul_assoc, mul_left_comm, mul_comm]

/-!
### Stronger same-level separation for “fixed last digit” blocks

The Appendix’s straight-wall families fix the last digit `cur` and vary only the prefix. In that
situation, the separation between left endpoints is controlled by the **prefix width** rather than
the full-cylinder width, yielding an extra factor `3` of slack. This is the key numerical input
for turning endpoint-only intersection control into true disjointness.
-/

theorem rwBlockLeft_separated_of_append_singleton_of_length_eq (k : ℤ) {pref pref' : List Bool}
    (hlen : pref.length = pref'.length) (hne : pref ≠ pref') (cur : Bool) :
    |rwBlockLeft k (pref ++ [cur]) - rwBlockLeft k (pref' ++ [cur])| ≥ 6 * rwBlockLen k (pref ++ [cur]) := by
  have hs : 0 ≤ headScale k := le_of_lt (headScale_pos k)
  have hsep : |cantorLeft (pref ++ [cur]) - cantorLeft (pref' ++ [cur])| ≥ 2 * cantorWidth pref :=
    cantorLeft_separated_append_singleton_of_length_eq (ds := pref) (ds' := pref') hlen hne cur
  have hscale :
      |rwBlockLeft k (pref ++ [cur]) - rwBlockLeft k (pref' ++ [cur])| =
        headScale k * |cantorLeft (pref ++ [cur]) - cantorLeft (pref' ++ [cur])| := by
    simp [rwBlockLeft, tau_sub, abs_mul, abs_of_nonneg hs, mul_assoc, mul_left_comm, mul_comm]
  have hscaled :
      headScale k * |cantorLeft (pref ++ [cur]) - cantorLeft (pref' ++ [cur])| ≥ headScale k * (2 * cantorWidth pref) :=
    mul_le_mul_of_nonneg_left hsep hs
  -- `6 * rwBlockLen k (pref++[cur]) = headScale k * (2 * cantorWidth pref)` since `cantorWidth (pref++[cur]) = cantorWidth pref / 3`.
  have hlenW : cantorWidth (pref ++ [cur]) = cantorWidth pref / 3 := by
    simp [cantorWidth, List.length_append, div_eq_mul_inv, pow_succ, mul_assoc, mul_left_comm, mul_comm]
  calc
    |rwBlockLeft k (pref ++ [cur]) - rwBlockLeft k (pref' ++ [cur])|
        = headScale k * |cantorLeft (pref ++ [cur]) - cantorLeft (pref' ++ [cur])| := hscale
    _ ≥ headScale k * (2 * cantorWidth pref) := hscaled
    _ = 6 * rwBlockLen k (pref ++ [cur]) := by
          simp [rwBlockLen, hlenW, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

theorem rwBlockLen_eq_of_length_eq (k : ℤ) {ds ds' : List Bool} (hlen : ds.length = ds'.length) :
    rwBlockLen k ds = rwBlockLen k ds' := by
  simp [rwBlockLen, cantorWidth, hlen]

/-- A convenient endpoint-separation inequality used in Appendix-style “no spurious collisions”
arguments: if two same-level blocks are distinct and ordered, the left endpoint of the right block
is at least one full block-length to the right of the right endpoint of the left block. -/
theorem rwBlockLeft_sub_right_ge_len_of_left_gt (k : ℤ) {ds ds' : List Bool}
    (hlen : ds.length = ds'.length) (hne : ds ≠ ds') (hgt : rwBlockLeft k ds' < rwBlockLeft k ds) :
    rwBlockLeft k ds - (rwBlockLeft k ds' + rwBlockLen k ds') ≥ rwBlockLen k ds := by
  -- Use the `2*len` separation, then subtract one length.
  have hsep : |rwBlockLeft k ds - rwBlockLeft k ds'| ≥ 2 * rwBlockLen k ds :=
    rwBlockLeft_separated_of_length_eq (k := k) (ds := ds) (ds' := ds') hlen hne
  have habs : rwBlockLeft k ds - rwBlockLeft k ds' ≥ 2 * rwBlockLen k ds := by
    -- When `ds` is to the right, the absolute value is the plain difference.
    have : 0 ≤ rwBlockLeft k ds - rwBlockLeft k ds' := by linarith
    simpa [abs_of_nonneg this, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsep
  -- Convert the length on the `ds'` side using the common length.
  have hlenEq : rwBlockLen k ds' = rwBlockLen k ds := (rwBlockLen_eq_of_length_eq (k := k) (ds := ds') (ds' := ds) hlen.symm)
  -- Finish by linear arithmetic.
  nlinarith [habs, hlenEq]

/-!
## Appendix-style endpoint inequalities (straight-wall prerequisites)

The Appendix rules out unintended straight-wall collisions by comparing block separation to
half-heights (endpoints) of wall segments. The next definition packages the numerical target.
-/

/-- Endpoint separation inequality: block `ds` is far enough to the right of `ds'` that
the x-distance between `left(ds)` and `right(ds')` dominates the sum of half-lengths. -/
def endpointSep (k : ℤ) (ds ds' : List Bool) : Prop :=
  rwBlockLeft k ds - (rwBlockLeft k ds' + rwBlockLen k ds') ≥ (rwBlockLen k ds) / 2 + (rwBlockLen k ds') / 2

theorem endpointSep_of_length_eq_of_left_gt (k : ℤ) {ds ds' : List Bool}
    (hlen : ds.length = ds'.length) (hne : ds ≠ ds') (hgt : rwBlockLeft k ds' < rwBlockLeft k ds) :
    endpointSep k ds ds' := by
  have hlenEq : rwBlockLen k ds' = rwBlockLen k ds :=
    rwBlockLen_eq_of_length_eq (k := k) (ds := ds') (ds' := ds) hlen.symm
  have hgap : rwBlockLeft k ds - (rwBlockLeft k ds' + rwBlockLen k ds') ≥ rwBlockLen k ds :=
    rwBlockLeft_sub_right_ge_len_of_left_gt (k := k) (ds := ds) (ds' := ds') hlen hne hgt
  dsimp [endpointSep]
  nlinarith [hgap, hlenEq]

/-!
### Cross-`k` endpoint separation (needed for full union avoidance)

The Appendix’s “no spurious collisions” inequalities compare endpoints of wall segments which may
live in *different* head intervals `I_k` and `I_{k'}`.

The original `endpointSep k ds ds'` is specialized to a common `k`. The following generalization
records the same numerical shape for two potentially different indices.
-/

/-- Cross-`k` endpoint separation inequality: the `k`-block lies far enough to the right of the
right endpoint of the `k'`-block. -/
def endpointSepCross (k : ℤ) (ds : List Bool) (k' : ℤ) (ds' : List Bool) : Prop :=
  rwBlockLeft k ds - (rwBlockLeft k' ds' + rwBlockLen k' ds') ≥ (rwBlockLen k ds) / 2 + (rwBlockLen k' ds') / 2

theorem rwBlockInterval_eq_image_tau (k : ℤ) (ds : List Bool) :
    rwBlockInterval k ds = (tau k) '' cantorCylinderInterval ds := by
  classical
  have hs : 0 < headScale k := headScale_pos k
  -- Compute the image under the explicit affine homeomorphism `x ↦ s*x + b`.
  have himage :
      (Topological.affineHomeomorph (headScale k) (tauOffset k) hs.ne') '' cantorCylinderInterval ds =
        Set.Icc (headScale k * cantorLeft ds + tauOffset k)
          (headScale k * (cantorLeft ds + cantorWidth ds) + tauOffset k) := by
    -- `cantorCylinderInterval ds` is an `Icc`, so `affineHomeomorph_image_Icc` applies.
    simpa [cantorCylinderInterval, Topological.affineHomeomorph_image_Icc, hs]
  -- Rewrite the RHS as the `rwBlockInterval` endpoints using `tau` and `rwBlockLen`.
  ext z
  constructor
  · intro hz
    have hz' :
        z ∈ (Topological.affineHomeomorph (headScale k) (tauOffset k) hs.ne') '' cantorCylinderInterval ds := by
      simpa [rwBlockInterval, rwBlockLeft, rwBlockLen, tau_eq_affine, tauOffset] using hz
    -- Convert membership in the computed image to membership in `tau '' cylinderInterval`.
    rcases hz' with ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    -- `affineHomeomorph` and `tau` have the same forward map.
    simp [Topological.affineHomeomorph, tau_eq_affine]
  · rintro ⟨x, hx, rfl⟩
    -- Go through the affine image computation.
    have : (Topological.affineHomeomorph (headScale k) (tauOffset k) hs.ne') (x) = tau k x := by
      simp [Topological.affineHomeomorph, tau_eq_affine]
    have hx' :
        tau k x ∈ (Topological.affineHomeomorph (headScale k) (tauOffset k) hs.ne') '' cantorCylinderInterval ds := by
      refine ⟨x, hx, by simpa [this]⟩
    -- Rewrite by `himage` and normalize the interval endpoints back to `rwBlockInterval`.
    have hx'' :
        tau k x ∈ Set.Icc (headScale k * cantorLeft ds + tauOffset k)
          (headScale k * (cantorLeft ds + cantorWidth ds) + tauOffset k) := by
      simpa [himage] using hx'
    -- Convert to the explicit `rwBlockInterval` bounds.
    simpa [rwBlockInterval, rwBlockLeft, rwBlockLen, tau_eq_affine, tauOffset, mul_add, add_assoc, add_left_comm,
      add_comm] using hx''

theorem rwBlockInterval_disjoint_of_length_eq (k : ℤ) {ds ds' : List Bool} (hlen : ds.length = ds'.length)
    (hne : ds ≠ ds') :
    Disjoint (rwBlockInterval k ds) (rwBlockInterval k ds') := by
  -- Disjointness is true already on the Cantor-side cylinder intervals, and `tau` is injective.
  have hd : Disjoint (cantorCylinderInterval ds) (cantorCylinderInterval ds') :=
    cantorCylinderInterval_disjoint_of_length_eq (ds := ds) (ds' := ds') hlen hne
  -- Transfer via image under an injective map.
  have hdImg : Disjoint ((tau k) '' cantorCylinderInterval ds) ((tau k) '' cantorCylinderInterval ds') :=
    Set.disjoint_image_of_injective (tau_injective k) hd
  -- Rewrite images to `rwBlockInterval`.
  simpa [rwBlockInterval_eq_image_tau (k := k) (ds := ds), rwBlockInterval_eq_image_tau (k := k) (ds := ds')] using hdImg

theorem rwBlockInterval_disjoint_of_rwDigits (k : ℤ) {pref pref' : List Bool} {cur cur' : Bool}
    (hL : pref.length = indexNat k) (hL' : pref'.length = indexNat k)
    (hne : pref ++ [cur] ≠ pref' ++ [cur']) :
    Disjoint (rwBlockInterval k (pref ++ [cur])) (rwBlockInterval k (pref' ++ [cur'])) := by
  -- Same `k` implies the two lists have the same length (`indexNat k + 1`).
  have hlen : (pref ++ [cur]).length = (pref' ++ [cur']).length := by
    simp [List.length_append, hL, hL']
  exact rwBlockInterval_disjoint_of_length_eq (k := k) (ds := pref ++ [cur]) (ds' := pref' ++ [cur']) hlen hne

theorem rwBlockInterval_eq_of_mem_of_rwDigits (k : ℤ) {pref pref' : List Bool} {cur cur' : Bool} {x : ℝ}
    (hL : pref.length = indexNat k) (hL' : pref'.length = indexNat k)
    (hx : x ∈ rwBlockInterval k (pref ++ [cur])) (hx' : x ∈ rwBlockInterval k (pref' ++ [cur'])) :
    pref ++ [cur] = pref' ++ [cur'] := by
  classical
  by_contra hne
  have hdis :
      Disjoint (rwBlockInterval k (pref ++ [cur])) (rwBlockInterval k (pref' ++ [cur'])) :=
    rwBlockInterval_disjoint_of_rwDigits (k := k) (pref := pref) (pref' := pref') (cur := cur) (cur' := cur')
      hL hL' hne
  exact (Set.disjoint_left.1 hdis) hx hx'

theorem rwBlockInterval_subset_headInterval (k : ℤ) (ds : List Bool) : rwBlockInterval k ds ⊆ headInterval k := by
  intro z hz
  -- Use the image description and the fact the cylinder interval lies in `[0,1]`.
  have hs : 0 < headScale k := headScale_pos k
  have hzImg : z ∈ (tau k) '' cantorCylinderInterval ds := by
    simpa [rwBlockInterval_eq_image_tau (k := k) (ds := ds)] using hz
  rcases hzImg with ⟨x, hx, rfl⟩
  have hx01 : x ∈ Set.Icc (0 : ℝ) 1 :=
    cantorCylinderInterval_subset_Icc ds hx
  exact tau_mem_headInterval (k := k) (x := x) hx01

theorem rwBlockInterval_disjoint_of_k_ne {k k' : ℤ} (hk : k ≠ k') (ds : List Bool) (ds' : List Bool) :
    Disjoint (rwBlockInterval k ds) (rwBlockInterval k' ds') := by
  -- Each `rwBlockInterval k ds` lies inside `headInterval k`, and head intervals are disjoint.
  have hsub : rwBlockInterval k ds ⊆ headInterval k := rwBlockInterval_subset_headInterval (k := k) ds
  have hsub' : rwBlockInterval k' ds' ⊆ headInterval k' := rwBlockInterval_subset_headInterval (k := k') ds'
  have hdis : Disjoint (headInterval k) (headInterval k') :=
    headInterval_disjoint (k := k) (k' := k') hk
  exact hdis.mono hsub hsub'

/-- Distinct blocks (same `k`, same `cur`) produce disjoint read-only wall segments. -/
theorem rwWall_disjoint_of_length_eq (k : ℤ) {ds ds' : List Bool} (hlen : ds.length = ds'.length) (hne : ds ≠ ds')
    (cur : Bool) :
    Disjoint (rwWall k ds cur) (rwWall k ds' cur) := by
  classical
  refine Set.disjoint_left.2 ?_
  intro p hp hp'
  have hx : x p ∈ rwBlockInterval k ds := hp.1
  have hx' : x p ∈ rwBlockInterval k ds' := hp'.1
  have hdis : Disjoint (rwBlockInterval k ds) (rwBlockInterval k ds') :=
    rwBlockInterval_disjoint_of_length_eq (k := k) (ds := ds) (ds' := ds') hlen hne
  exact (Set.disjoint_left.1 hdis) hx hx'

theorem mem_tildeWall_iff (k : ℤ) (ds : List Bool) (cur : Bool) (p : V) :
    p ∈ tildeWall k ds cur ↔ (x p - shift cur) ∈ rwBlockInterval k ds ∧
      y p =
        (2 : ℝ) +
          (if cur then (-rwBlockCenter k ds + (x p - shift cur)) else (rwBlockCenter k ds - (x p - shift cur))) := by
  -- Pure algebra on the `x`-interval condition.
  constructor <;> intro hp
  · rcases hp with ⟨hx, hy⟩
    refine ⟨?_, hy⟩
    -- `x ∈ [left+shift, left+shift+len]` iff `x-shift ∈ [left, left+len]`.
    rcases hx with ⟨hxL, hxU⟩
    constructor <;> linarith
  · rcases hp with ⟨hx, hy⟩
    refine ⟨?_, hy⟩
    rcases hx with ⟨hxL, hxU⟩
    constructor <;> linarith

/-- Distinct blocks (same `k`, same `cur`) produce disjoint redirecting wall segments. -/
theorem tildeWall_disjoint_of_length_eq (k : ℤ) {ds ds' : List Bool} (hlen : ds.length = ds'.length) (hne : ds ≠ ds')
    (cur : Bool) :
    Disjoint (tildeWall k ds cur) (tildeWall k ds' cur) := by
  classical
  refine Set.disjoint_left.2 ?_
  intro p hp hp'
  have hx : (x p - shift cur) ∈ rwBlockInterval k ds := (mem_tildeWall_iff (k := k) (ds := ds) (cur := cur) (p := p)).1 hp |>.1
  have hx' : (x p - shift cur) ∈ rwBlockInterval k ds' := (mem_tildeWall_iff (k := k) (ds := ds') (cur := cur) (p := p)).1 hp' |>.1
  have hdis : Disjoint (rwBlockInterval k ds) (rwBlockInterval k ds') :=
    rwBlockInterval_disjoint_of_length_eq (k := k) (ds := ds) (ds' := ds') hlen hne
  exact (Set.disjoint_left.1 hdis) hx hx'

/-- Distinct blocks (same `k`, same `cur`) produce disjoint rewrite wall segments. -/
theorem rwWallRewrite_disjoint_of_length_eq (k : ℤ) {ds ds' : List Bool} (hlen : ds.length = ds'.length)
    (hne : ds ≠ ds') (cur : Bool) :
    Disjoint (rwWallRewrite k ds cur) (rwWallRewrite k ds' cur) := by
  classical
  refine Set.disjoint_left.2 ?_
  intro p hp hp'
  have hx : x p ∈ rwBlockInterval k ds := hp.1
  have hx' : x p ∈ rwBlockInterval k ds' := hp'.1
  have hdis : Disjoint (rwBlockInterval k ds) (rwBlockInterval k ds') :=
    rwBlockInterval_disjoint_of_length_eq (k := k) (ds := ds) (ds' := ds') hlen hne
  exact (Set.disjoint_left.1 hdis) hx hx'

end PaperReadWrite

end Billiards
end MirandaDynamics
end HeytingLean
