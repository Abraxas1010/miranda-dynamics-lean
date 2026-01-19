import HeytingLean.MirandaDynamics.Billiards.CantorDigits

/-!
# MirandaDynamics.Billiards: explicit Cantor cylinder sets (WS7.4 support)

`CantorDigits.lean` defines partial digit readers `cantorHeadDigit?` / `cantorTail?` and the
iterated digit reader `cantorDigitAt?`.

For “paper-faithful” piecewise-affine statements it is convenient to also have *explicit* cylinder
sets: sets of reals whose ternary expansion has a fixed finite prefix in `{0,2}`.

This file defines those cylinder sets recursively via affine preimages of the left/right thirds and
proves a basic correctness lemma: on a cylinder set, the digit reader returns the fixed digits.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set

/-- The closed “head interval” corresponding to the leading Cantor digit `b` (`0` for `false`,
`2` for `true`). -/
def cantorHeadInterval (b : Bool) : Set ℝ :=
  if b then Set.Icc twoThird 1 else Set.Icc (0 : ℝ) oneThird

/-- The affine tail update used after fixing the leading digit `b`. -/
def cantorTailAffine (b : Bool) (x : ℝ) : ℝ :=
  if b then 3 * x - 2 else 3 * x

/-- The Cantor cylinder set determined by a finite digit list `ds` (0-based, leading digit first). -/
def cantorCylinder : List Bool → Set ℝ
  | [] => Set.Icc (0 : ℝ) 1
  | b :: ds => { x | x ∈ cantorHeadInterval b ∧ cantorTailAffine b x ∈ cantorCylinder ds }

theorem cantorHeadInterval_disjoint : Disjoint (cantorHeadInterval false) (cantorHeadInterval true) := by
  -- `[0, 1/3]` and `[2/3, 1]` are disjoint.
  refine Set.disjoint_left.2 ?_
  intro x hxF hxT
  have hxF' : x ∈ Set.Icc (0 : ℝ) oneThird := by
    simpa [cantorHeadInterval] using hxF
  have hxT' : x ∈ Set.Icc twoThird 1 := by
    simpa [cantorHeadInterval] using hxT
  have hlt : (oneThird : ℝ) < twoThird := by
    norm_num [oneThird, twoThird]
  exact (not_lt_of_ge (le_trans hxT'.1 hxF'.2)) hlt

theorem cantorCylinder_eq_of_mem_of_length_eq :
    ∀ (ds ds' : List Bool) {x : ℝ},
      x ∈ cantorCylinder ds → x ∈ cantorCylinder ds' → ds.length = ds'.length → ds = ds' := by
  intro ds
  induction ds with
  | nil =>
      intro ds' x hx hx' hlen
      cases ds' with
      | nil => rfl
      | cons b tl =>
          cases hlen
  | cons b ds ih =>
      intro ds' x hx hx' hlen
      cases ds' with
      | nil =>
          cases hlen
      | cons b' ds' =>
          -- Heads must agree, otherwise `x` lies in disjoint head intervals.
          have hb : b = b' := by
            cases b <;> cases b' <;> try rfl
            · -- `false ≠ true`
              exfalso
              exact (Set.disjoint_left.1 cantorHeadInterval_disjoint) hx.1 hx'.1
            · -- `true ≠ false`
              exfalso
              exact (Set.disjoint_left.1 cantorHeadInterval_disjoint) hx'.1 hx.1
          subst hb
          have hlen' : ds.length = ds'.length := Nat.succ.inj hlen
          have hxT : cantorTailAffine b x ∈ cantorCylinder ds := hx.2
          have hxT' : cantorTailAffine b x ∈ cantorCylinder ds' := by
            -- `b' = b` already substituted.
            simpa using hx'.2
          have hrec : ds = ds' := ih ds' (x := cantorTailAffine b x) hxT hxT' hlen'
          simp [hrec]

theorem cantorCylinder_disjoint_of_length_eq {ds ds' : List Bool} (hlen : ds.length = ds'.length)
    (hne : ds ≠ ds') : Disjoint (cantorCylinder ds) (cantorCylinder ds') := by
  refine Set.disjoint_left.2 ?_
  intro x hx hx'
  have : ds = ds' :=
    cantorCylinder_eq_of_mem_of_length_eq ds ds' (x := x) hx hx' hlen
  exact hne this

theorem cantorHeadDigit?_eq_some_of_mem_headInterval {b : Bool} {x : ℝ} (hx : x ∈ cantorHeadInterval b) :
    cantorHeadDigit? x = some b := by
  cases b with
  | false =>
    -- `x ≤ 1/3` triggers the first branch.
    have hx' : x ∈ Set.Icc (0 : ℝ) oneThird := by
      simpa [cantorHeadInterval] using hx
    have hxle : x ≤ oneThird := hx'.2
    simp [cantorHeadDigit?, hxle]
  | true =>
    -- `2/3 ≤ x` triggers the second branch, and also rules out `x ≤ 1/3`.
    have hx' : x ∈ Set.Icc twoThird 1 := by
      simpa [cantorHeadInterval] using hx
    have hlt : (oneThird : ℝ) < twoThird := by
      norm_num [oneThird, twoThird]
    have hxne : ¬ x ≤ oneThird := by
      exact not_le_of_gt (lt_of_lt_of_le hlt hx'.1)
    have hxge : twoThird ≤ x := hx'.1
    simp [cantorHeadDigit?, hxne, hxge]

theorem cantorTail?_eq_some_of_mem_headInterval {b : Bool} {x : ℝ} (hx : x ∈ cantorHeadInterval b) :
    cantorTail? x = some (cantorTailAffine b x) := by
  have hhd : cantorHeadDigit? x = some b := cantorHeadDigit?_eq_some_of_mem_headInterval (b := b) hx
  cases b <;> simp [cantorTail?, cantorTailAffine, hhd]

theorem cantorDigitAt?_eq_get?_of_mem_cantorCylinder (ds : List Bool) {x : ℝ} (hx : x ∈ cantorCylinder ds) :
    ∀ n : Nat, n < ds.length → cantorDigitAt? n x = ds[n]? := by
  induction ds generalizing x with
  | nil =>
    intro n hn
    cases hn
  | cons b ds ih =>
    intro n hn
    have hxH : x ∈ cantorHeadInterval b := hx.1
    have hxT : cantorTailAffine b x ∈ cantorCylinder ds := hx.2
    cases n with
    | zero =>
      simp [cantorDigitAt?, cantorHeadDigit?_eq_some_of_mem_headInterval (b := b) hxH]
    | succ n =>
      have htail : cantorTail? x = some (cantorTailAffine b x) :=
        cantorTail?_eq_some_of_mem_headInterval (b := b) hxH
      have hn' : n < ds.length := Nat.lt_of_succ_lt_succ hn
      simpa [cantorDigitAt?, htail] using ih (x := cantorTailAffine b x) hxT n hn'

private theorem getOpt_append_length_singleton (pref : List Bool) (b : Bool) :
    (pref ++ [b])[pref.length]? = some b := by
  induction pref with
  | nil => simp
  | cons a tl ih =>
    simp

/-- The set of points whose `n`-th Cantor digit is `cur` (with no restriction on earlier digits),
expressed as a union of cylinder sets. -/
def cantorDigitBlock (n : Nat) (cur : Bool) : Set ℝ :=
  { x | ∃ pref : List Bool, pref.length = n ∧ x ∈ cantorCylinder (pref ++ [cur]) }

theorem cantorDigitAt?_eq_some_of_mem_cantorDigitBlock {n : Nat} {cur : Bool} {x : ℝ}
    (hx : x ∈ cantorDigitBlock n cur) : cantorDigitAt? n x = some cur := by
  rcases hx with ⟨pref, hlen, hxCyl⟩
  have hn : n < (pref ++ [cur]).length := by
    cases hlen
    simp [List.length_append]
  have hread :
      cantorDigitAt? n x = (pref ++ [cur])[n]? :=
    cantorDigitAt?_eq_get?_of_mem_cantorCylinder (ds := pref ++ [cur]) (x := x) hxCyl n hn
  -- The element at index `n = prefix.length` of `prefix ++ [cur]` is exactly `cur`.
  have hget : (pref ++ [cur])[n]? = some cur := by
    cases hlen
    exact getOpt_append_length_singleton pref cur
  simpa [hget] using hread

end Billiards
end MirandaDynamics
end HeytingLean
