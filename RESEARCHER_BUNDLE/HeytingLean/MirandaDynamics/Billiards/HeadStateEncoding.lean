import HeytingLean.MirandaDynamics.Billiards.CantorEncoding

/-!
# MirandaDynamics.Billiards: refining the head coordinate to carry finite control state

`CantorEncoding.lean` embeds head positions `k : ℤ` into disjoint intervals `headInterval k` via `τ_k`.

To encode a *finite control state* (e.g. a machine state) in the same head coordinate, we further
subdivide each `headInterval k` into `m` disjoint *open* subintervals indexed by `q : Fin m`.

We keep the decoder partial (returns `none` on boundaries), mirroring the project’s “good phase
space” philosophy: the dynamics will be proved to avoid these boundary points.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set

/-! ## State subintervals inside a head interval -/

/-- Left endpoint for the state subinterval `(k,q)` inside `headInterval k`. -/
noncomputable def headStateLeft (m : ℕ) (k : ℤ) (q : Fin m) : ℝ :=
  headLeft k + headScale k * ((q.1 : ℝ) / (m : ℝ))

/-- Right endpoint for the state subinterval `(k,q)` inside `headInterval k`. -/
noncomputable def headStateRight (m : ℕ) (k : ℤ) (q : Fin m) : ℝ :=
  headLeft k + headScale k * (((q.1 + 1 : ℕ) : ℝ) / (m : ℝ))

/-- The (open) state subinterval `(k,q)` used to carry finite control in the head coordinate. -/
noncomputable def headStateInterval (m : ℕ) (k : ℤ) (q : Fin m) : Set ℝ :=
  Set.Ioo (headStateLeft m k q) (headStateRight m k q)

theorem headStateInterval_subset_headInterval {m : ℕ} {k : ℤ} {q : Fin m} {z : ℝ}
    (hz : z ∈ headStateInterval m k q) : z ∈ headInterval k := by
  have hspos : 0 < headScale k := headScale_pos k
  have hs0 : 0 ≤ headScale k := le_of_lt hspos
  have hmne : m ≠ 0 := by
    intro hm0
    subst hm0
    exact (Nat.not_lt_zero q.1) q.2
  have hm : 0 < (m : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero hmne)
  have hq0 : 0 ≤ ((q.1 : ℝ) / (m : ℝ)) := by
    have : (0 : ℝ) ≤ (q.1 : ℝ) := by positivity
    exact div_nonneg this (le_of_lt hm)
  have hq1 : ((q.1 + 1 : ℕ) : ℝ) / (m : ℝ) ≤ 1 := by
    have hlt : q.1 + 1 ≤ m := Nat.succ_le_of_lt q.2
    have : ((q.1 + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlt
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
    simpa using (div_le_one_of_le₀ this hm0)
  have hL : headLeft k ≤ z := by
    have hzL : headLeft k + headScale k * ((q.1 : ℝ) / (m : ℝ)) < z := by
      simpa [headStateInterval, headStateLeft] using hz.1
    have hbase : headLeft k ≤ headLeft k + headScale k * ((q.1 : ℝ) / (m : ℝ)) := by
      have : 0 ≤ headScale k * ((q.1 : ℝ) / (m : ℝ)) := mul_nonneg hs0 hq0
      linarith
    exact le_of_lt (lt_of_le_of_lt hbase hzL)
  have hR : z ≤ headRight k := by
    have hz' : z < headLeft k + headScale k * (((q.1 + 1 : ℕ) : ℝ) / (m : ℝ)) := by
      simpa [headStateInterval, headStateRight] using hz.2
    have hbound :
        headLeft k + headScale k * (((q.1 + 1 : ℕ) : ℝ) / (m : ℝ)) ≤ headRight k := by
      -- Use `headRight - headLeft = headScale` (so `headRight = headLeft + headScale`).
      have hlen : headRight k = headLeft k + headScale k := by
        have := headInterval_length (k := k)
        linarith
      -- `headScale * frac ≤ headScale` since `frac ≤ 1`.
      have : headScale k * (((q.1 + 1 : ℕ) : ℝ) / (m : ℝ)) ≤ headScale k := by
        simpa [one_mul] using mul_le_mul_of_nonneg_left hq1 hs0
      simpa [hlen, add_assoc] using add_le_add_left this (headLeft k)
    exact le_of_lt (lt_of_lt_of_le hz' hbound)
  exact ⟨hL, hR⟩

/-! ## An “interior” embedding to avoid boundary ambiguity -/

/-- An interior affine reparameterization of `[0,1]` into `(0,1)`: `inset x = (x+1)/3`. -/
noncomputable def inset (x : ℝ) : ℝ :=
  (x + 1) / 3

private theorem inset_pos {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : 0 < inset x := by
  have : (1 / 3 : ℝ) ≤ inset x := by
    have hx0 : (1 : ℝ) ≤ x + 1 := by linarith [hx.1]
    have : (1 : ℝ) / 3 ≤ (x + 1) / 3 :=
      div_le_div_of_nonneg_right hx0 (by norm_num : (0 : ℝ) ≤ 3)
    simpa [inset] using this
  have : (0 : ℝ) < inset x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 / 3 : ℝ)) this
  simpa using this

private theorem inset_lt_one {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : inset x < 1 := by
  have : inset x ≤ (2 / 3 : ℝ) := by
    have hx1 : x + 1 ≤ (2 : ℝ) := by linarith [hx.2]
    have : (x + 1) / 3 ≤ (2 : ℝ) / 3 :=
      div_le_div_of_nonneg_right hx1 (by norm_num : (0 : ℝ) ≤ 3)
    simpa [inset] using this
  exact lt_of_le_of_lt this (by norm_num)

/-- A refined head embedding carrying a state index `q : Fin m`.

We embed the tape coordinate `x ∈ [0,1]` into the *interior* of the `q`-th subinterval via
`inset x = (x+1)/3 ∈ (0,1)`, ensuring we never hit subinterval boundaries on encoded points. -/
noncomputable def tauState (m : ℕ) (k : ℤ) (q : Fin m) (x : ℝ) : ℝ :=
  headLeft k + headScale k * (((q.1 : ℝ) + inset x) / (m : ℝ))

theorem tauState_mem_headStateInterval {m : ℕ} (hm : 0 < m) (k : ℤ) (q : Fin m) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : tauState m k q x ∈ headStateInterval m k q := by
  have hspos : 0 < headScale k := headScale_pos k
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hin0 : 0 < inset x := inset_pos (x := x) hx
  have hin1 : inset x < 1 := inset_lt_one (x := x) hx
  have hdiv0 : ((q.1 : ℝ) / (m : ℝ)) < ((q.1 : ℝ) + inset x) / (m : ℝ) := by
    have : (q.1 : ℝ) < (q.1 : ℝ) + inset x := by linarith
    exact div_lt_div_of_pos_right this hmpos
  have hdiv1 :
      ((q.1 : ℝ) + inset x) / (m : ℝ) < (((q.1 + 1 : ℕ) : ℝ) / (m : ℝ)) := by
    have : (q.1 : ℝ) + inset x < (q.1 : ℝ) + 1 := by linarith
    have : (q.1 : ℝ) + inset x < ((q.1 + 1 : ℕ) : ℝ) := by
      simpa using this
    exact div_lt_div_of_pos_right this hmpos
  have hmul0 : headScale k * ((q.1 : ℝ) / (m : ℝ)) < headScale k * (((q.1 : ℝ) + inset x) / (m : ℝ)) :=
    mul_lt_mul_of_pos_left hdiv0 hspos
  have hmul1 :
      headScale k * (((q.1 : ℝ) + inset x) / (m : ℝ)) <
        headScale k * (((q.1 + 1 : ℕ) : ℝ) / (m : ℝ)) :=
    mul_lt_mul_of_pos_left hdiv1 hspos
  refine ⟨?_, ?_⟩
  · simpa [headStateInterval, headStateLeft, tauState, inset, add_assoc, add_left_comm, add_comm] using
      (add_lt_add_left hmul0 (headLeft k))
  · simpa [headStateInterval, headStateRight, tauState, inset, add_assoc, add_left_comm, add_comm] using
      (add_lt_add_left hmul1 (headLeft k))

/-- Refined head encoding carrying a finite control state. -/
noncomputable def encodeWithHeadState (m : ℕ) (t : Tape) (k : ℤ) (q : Fin m) : ℝ :=
  tauState m k q (encodeTape t)

theorem encodeWithHeadState_mem_headStateInterval {m : ℕ} (hm : 0 < m) (t : Tape) (k : ℤ) (q : Fin m) :
    encodeWithHeadState m t k q ∈ headStateInterval m k q := by
  have hx : encodeTape t ∈ Set.Icc (0 : ℝ) 1 := encodeTape_mem_Icc t
  simpa [encodeWithHeadState] using
    (tauState_mem_headStateInterval (m := m) hm (k := k) (q := q) (x := encodeTape t) hx)

/-! ## A partial decoder for `(k,q)` -/

noncomputable def headIndexState? (m : ℕ) (z : ℝ) : Option (ℤ × Fin m) := by
  classical
  exact if h : ∃ kq : ℤ × Fin m, z ∈ headStateInterval m kq.1 kq.2 then some (Classical.choose h) else none

theorem headStateInterval_disjoint_of_ne {m : ℕ} (hm : 0 < m) (kq kq' : ℤ × Fin m) (hne : kq ≠ kq') :
    Disjoint (headStateInterval m kq.1 kq.2) (headStateInterval m kq'.1 kq'.2) := by
  classical
  by_cases hk : kq.1 = kq'.1
  ·
    have hq : kq.2 ≠ kq'.2 := by
      intro hqq
      exact hne (Prod.ext hk hqq)
    have hqval : kq.2.1 ≠ kq'.2.1 := by
      intro hval
      apply hq
      exact Fin.ext hval
    have hlt : kq.2.1 < kq'.2.1 ∨ kq'.2.1 < kq.2.1 := lt_or_gt_of_ne hqval
    rcases hlt with hlt | hgt
    · -- `q < q'` gives `right(q) ≤ left(q')`, hence disjoint `Ioo`.
      have hsucc : kq.2.1 + 1 ≤ kq'.2.1 := Nat.succ_le_of_lt hlt
      have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
      have hs0 : 0 ≤ headScale kq.1 := le_of_lt (headScale_pos kq.1)
      have hdiv :
          (((kq.2.1 + 1 : ℕ) : ℝ) / (m : ℝ)) ≤ ((kq'.2.1 : ℝ) / (m : ℝ)) := by
        have : ((kq.2.1 + 1 : ℕ) : ℝ) ≤ (kq'.2.1 : ℝ) := by exact_mod_cast hsucc
        exact div_le_div_of_nonneg_right this (le_of_lt hmpos)
      have hmul :
          headScale kq.1 * (((kq.2.1 + 1 : ℕ) : ℝ) / (m : ℝ)) ≤ headScale kq.1 * ((kq'.2.1 : ℝ) / (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiv hs0
      have hsep :
          headStateRight m kq.1 kq.2 ≤ headStateLeft m kq'.1 kq'.2 := by
        simpa [headStateLeft, headStateRight, hk, add_assoc, add_left_comm, add_comm] using
          add_le_add_left hmul (headLeft kq.1)
      refine Set.disjoint_left.2 ?_
      intro z hz hz'
      have hz_lt : z < headStateRight m kq.1 kq.2 := by
        simpa [headStateInterval] using hz.2
      have hz'_gt : headStateLeft m kq'.1 kq'.2 < z := by
        simpa [headStateInterval] using hz'.1
      have : headStateLeft m kq'.1 kq'.2 < headStateRight m kq.1 kq.2 :=
        lt_trans hz'_gt hz_lt
      exact (not_lt_of_ge hsep) this
    · -- symmetric case
      have hsucc : kq'.2.1 + 1 ≤ kq.2.1 := Nat.succ_le_of_lt hgt
      have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
      have hs0 : 0 ≤ headScale kq.1 := le_of_lt (headScale_pos kq.1)
      have hdiv :
          (((kq'.2.1 + 1 : ℕ) : ℝ) / (m : ℝ)) ≤ ((kq.2.1 : ℝ) / (m : ℝ)) := by
        have : ((kq'.2.1 + 1 : ℕ) : ℝ) ≤ (kq.2.1 : ℝ) := by exact_mod_cast hsucc
        exact div_le_div_of_nonneg_right this (le_of_lt hmpos)
      have hmul :
          headScale kq.1 * (((kq'.2.1 + 1 : ℕ) : ℝ) / (m : ℝ)) ≤ headScale kq.1 * ((kq.2.1 : ℝ) / (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiv hs0
      have hsep :
          headStateRight m kq'.1 kq'.2 ≤ headStateLeft m kq.1 kq.2 := by
        simpa [headStateLeft, headStateRight, hk, add_assoc, add_left_comm, add_comm] using
          add_le_add_left hmul (headLeft kq.1)
      refine Set.disjoint_left.2 ?_
      intro z hz hz'
      have hz'_lt : z < headStateRight m kq'.1 kq'.2 := by
        simpa [headStateInterval] using hz'.2
      have hz_gt : headStateLeft m kq.1 kq.2 < z := by
        simpa [headStateInterval] using hz.1
      have : headStateLeft m kq.1 kq.2 < headStateRight m kq'.1 kq'.2 :=
        lt_trans hz_gt hz'_lt
      exact (not_lt_of_ge hsep) this
  · -- Different head indices: reduce to disjointness of `headInterval`.
    have hkne : kq.1 ≠ kq'.1 := hk
    have hdis : Disjoint (headInterval kq.1) (headInterval kq'.1) :=
      headInterval_disjoint kq.1 kq'.1 hkne
    refine Set.disjoint_left.2 ?_
    intro z hz hz'
    have hz1 : z ∈ headInterval kq.1 :=
      headStateInterval_subset_headInterval (m := m) (k := kq.1) (q := kq.2) (z := z) hz
    have hz2 : z ∈ headInterval kq'.1 :=
      headStateInterval_subset_headInterval (m := m) (k := kq'.1) (q := kq'.2) (z := z) hz'
    exact (Set.disjoint_left.1 hdis) hz1 hz2

theorem headIndexState?_eq_some_of_mem {m : ℕ} (hm : 0 < m) {z : ℝ} {kq : ℤ × Fin m}
    (hz : z ∈ headStateInterval m kq.1 kq.2) : headIndexState? m z = some kq := by
  classical
  have h : ∃ kq' : ℤ × Fin m, z ∈ headStateInterval m kq'.1 kq'.2 := ⟨kq, hz⟩
  have hz' :
      z ∈ headStateInterval m (Classical.choose h).1 (Classical.choose h).2 := Classical.choose_spec h
  have hkq : Classical.choose h = kq := by
    by_contra hne
    have hdis :
        Disjoint (headStateInterval m (Classical.choose h).1 (Classical.choose h).2)
          (headStateInterval m kq.1 kq.2) :=
      headStateInterval_disjoint_of_ne (m := m) hm (Classical.choose h) kq hne
    exact (Set.disjoint_left.1 hdis) hz' hz
  simp [headIndexState?, h, hkq]

theorem headIndexState?_encodeWithHeadState {m : ℕ} (hm : 0 < m) (t : Tape) (k : ℤ) (q : Fin m) :
    headIndexState? m (encodeWithHeadState m t k q) = some (k, q) := by
  have hx : encodeTape t ∈ Set.Icc (0 : ℝ) 1 := encodeTape_mem_Icc t
  have hz :
      tauState m k q (encodeTape t) ∈ headStateInterval m k q :=
    tauState_mem_headStateInterval (m := m) hm k q (x := encodeTape t) hx
  simpa [encodeWithHeadState] using (headIndexState?_eq_some_of_mem (m := m) hm (z := tauState m k q (encodeTape t))
    (kq := (k, q)) hz)

end Billiards
end MirandaDynamics
end HeytingLean
