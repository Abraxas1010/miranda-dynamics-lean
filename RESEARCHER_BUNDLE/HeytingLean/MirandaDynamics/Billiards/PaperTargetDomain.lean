import HeytingLean.MirandaDynamics.Billiards.PaperMapFiniteControlBlocks

/-!
# MirandaDynamics.Billiards: the WS7.4 paper-map branch domain (`CtrlDomain`)

This file isolates the WS7.4 “paper target” domain/lemmas from the WS7.3 billiard geometry work.

It deliberately does **not** depend on any concrete billiard table; it is just the analytic/coding
side describing where the piecewise-affine map `paperFctrl?` is defined.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set
open HeytingLean.MirandaDynamics.Computation

/-! ## The WS7.4 branch domain as a single set -/

def CtrlDomain (m : ℕ) : Set (ℝ × ℝ) :=
  { p | ∃ k : ℤ, ∃ q : Fin m, ∃ cur : Bool, p ∈ CtrlCantorBlock m k q cur }

theorem mem_CtrlDomain_of_paperFctrl?_eq_some {m : ℕ} (next : Fin m → Bool → Fin m × Bool × ℤ)
    {p p' : ℝ × ℝ} (h : paperFctrl? next p = some p') :
    p ∈ CtrlDomain m := by
  classical
  rcases p with ⟨x, z⟩
  unfold paperFctrl? at h
  cases h1 : headIndexState? m z with
  | none =>
    simp [h1] at h
  | some kq =>
    cases h2 : cantorDigitAt? (indexNat kq.1) x with
    | none =>
      simp [h1, h2] at h
    | some cur =>
      refine ⟨kq.1, kq.2, cur, ?_⟩
      have hz : z ∈ headStateInterval m kq.1 kq.2 := by
        -- `headIndexState?` chose `(kq)` witnessing membership.
        have hex : ∃ kq' : ℤ × Fin m, z ∈ headStateInterval m kq'.1 kq'.2 := by
          by_contra hex'
          have : headIndexState? m z = none := by
            unfold headIndexState?
            simp [hex']
          exact Option.noConfusion (this.symm.trans h1)
        have hchoose : Classical.choose hex = kq := by
          unfold headIndexState? at h1
          have : (some (Classical.choose hex) : Option (ℤ × Fin m)) = some kq := by
            simpa [hex] using h1
          exact Option.some.inj this
        simpa [hchoose] using Classical.choose_spec hex
      have hcur : cantorDigitAt? (indexNat kq.1) x = some cur := h2
      simp [CtrlCantorBlock, hz, hcur]

theorem paperFctrl?_eq_none_of_not_mem_CtrlDomain {m : ℕ} (next : Fin m → Bool → Fin m × Bool × ℤ)
    {p : ℝ × ℝ} (hp : p ∉ CtrlDomain m) :
    paperFctrl? next p = none := by
  cases h : paperFctrl? next p with
  | none => rfl
  | some p' =>
    have : p ∈ CtrlDomain m :=
      mem_CtrlDomain_of_paperFctrl?_eq_some (m := m) (next := next) (p := p) (p' := p') h
    exact False.elim (hp this)

/-! ## A local “branchwise” ext lemma (used when the billiard map is proved affine on blocks) -/

theorem eq_paperFctrl?_of_branchwise {m : ℕ} (hm : 0 < m) (next : Fin m → Bool → Fin m × Bool × ℤ)
    (R? : (ℝ × ℝ) → Option (ℝ × ℝ))
    (hbranch :
      ∀ {k : ℤ} {q : Fin m} {cur : Bool} {p : ℝ × ℝ},
        p ∈ CtrlCantorBlock m k q cur → R? p = some (paperFctrlAffine next k q cur p))
    (hnone : ∀ p : ℝ × ℝ, p ∉ CtrlDomain m → R? p = none) :
    ∀ p : ℝ × ℝ, R? p = paperFctrl? next p := by
  intro p
  by_cases hp : p ∈ CtrlDomain m
  · rcases hp with ⟨k, q, cur, hp⟩
    have hR : R? p = some (paperFctrlAffine next k q cur p) := hbranch (p := p) hp
    have hP : paperFctrl? next p = some (paperFctrlAffine next k q cur p) :=
      paperFctrl?_eq_some_paperFctrlAffine_of_mem (m := m) hm (next := next) (k := k) (q := q) (cur := cur) (p := p) hp
    simp [hR, hP]
  · have hR : R? p = none := hnone p hp
    have hP : paperFctrl? next p = none :=
      paperFctrl?_eq_none_of_not_mem_CtrlDomain (m := m) (next := next) (p := p) hp
    simp [hR, hP]

end Billiards
end MirandaDynamics
end HeytingLean

