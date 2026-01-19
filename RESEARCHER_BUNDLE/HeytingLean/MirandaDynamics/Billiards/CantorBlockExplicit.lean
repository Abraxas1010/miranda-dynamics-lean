import HeytingLean.MirandaDynamics.Billiards.CantorBlocks
import HeytingLean.MirandaDynamics.Billiards.CantorCylinders

/-!
# MirandaDynamics.Billiards: explicit Cantor blocks in `ℝ²` (WS7.4)

`CantorBlocks.lean` defines blocks using the digit reader predicate
`cantorDigitAt? (indexNat k) x = some cur`.

This file provides an *explicit* alternative description: the set of tape coordinates whose
`indexNat k`-th digit is `cur` is a union of finite cylinder sets (`CantorCylinders.lean`), and
membership implies the digit-reader condition needed to use the affine-piece theorem.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set

/-- An “explicit” Cantor block: head coordinate in `headInterval k`, and tape coordinate in the
explicit digit-block set selecting the `indexNat k`-th digit. -/
def CantorBlockExplicit (k : ℤ) (cur : Bool) : Set (ℝ × ℝ) :=
  { p | p.2 ∈ headInterval k ∧ p.1 ∈ cantorDigitBlock (indexNat k) cur }

theorem CantorBlockExplicit_subset_CantorBlock (k : ℤ) (cur : Bool) :
    CantorBlockExplicit k cur ⊆ CantorBlock k cur := by
  intro p hp
  refine ⟨hp.1, ?_⟩
  -- Use the explicit digit-block lemma.
  exact cantorDigitAt?_eq_some_of_mem_cantorDigitBlock (n := indexNat k) (cur := cur) (x := p.1) hp.2

theorem paperFgen?_eq_some_paperFgenAffine_of_mem_explicit (next : Bool → Bool × ℤ) {k : ℤ} {cur : Bool}
    {p : ℝ × ℝ} (hp : p ∈ CantorBlockExplicit k cur) :
    paperFgen? next p = some (paperFgenAffine next k cur p) := by
  apply paperFgen?_eq_some_paperFgenAffine_of_mem (next := next)
  exact CantorBlockExplicit_subset_CantorBlock k cur hp

end Billiards
end MirandaDynamics
end HeytingLean

