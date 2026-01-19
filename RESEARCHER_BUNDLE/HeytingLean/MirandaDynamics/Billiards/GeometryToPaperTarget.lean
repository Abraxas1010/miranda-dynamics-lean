import HeytingLean.MirandaDynamics.Billiards.PaperMapFiniteControlConjugacy
import HeytingLean.MirandaDynamics.Billiards.PartialMapIterate
import HeytingLean.MirandaDynamics.Billiards.PaperTargetDomain
import HeytingLean.MirandaDynamics.Billiards.UnitSquareMap

/-!
# MirandaDynamics.Billiards: scaffolding for WS7.3 → WS7.4 link

WS7.4 provides a symbolic target map on `ℝ²` (`paperFctrl?`) that is explicitly piecewise-affine on
control Cantor blocks.

WS7.3 provides a deterministic (partial) billiard map (`UnitSquareMap.next?`) on collision states.

This file does **not** construct the billiard coding from the paper (long-horizon), but it sets up
the interface and reduction lemmas needed to prove:

> “billiard return map = the WS7.4 piecewise-affine map on the invariant set”.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set

/-! ## WS7.3 → WS7.4 link as a one-step semiconjugacy interface -/

namespace UnitSquareMap

open HeytingLean.MirandaDynamics.Billiards.UnitSquareMap
open HeytingLean.MirandaDynamics.Billiards

structure PaperLink (m : ℕ) (next : Fin m → Bool → Fin m × Bool × ℤ) where
  /-- Coding of billiard collision states into the WS7.4 plane coordinates. -/
  encode : CollisionState → ℝ × ℝ
  /-- On “good” billiard states, the coding lands in the WS7.4 branch domain. -/
  encode_mem : ∀ s : CollisionState, Good s → encode s ∈ CtrlDomain m
  /-- One-step semiconjugacy: the billiard next-collision map matches the WS7.4 paper map. -/
  semiconj : ∀ s : CollisionState, Good s → Option.map encode (next? s) = paperFctrl? next (encode s)

/-! ## Iteration scaffolding for semiconjugacy (used by the return-map equality) -/

theorem nextIter?_exists_good_of_goodClosed {s s' : CollisionState} (hs : Good s)
    (hstep : next? s = some s') (hgoodClosed : ∀ {a a' : CollisionState}, Good a → next? a = some a' → Good a') :
    Good s' :=
  hgoodClosed hs hstep

theorem nextIter?_exists_good (hgoodClosed : ∀ {a a' : CollisionState}, Good a → next? a = some a' → Good a') :
    ∀ n : Nat, ∀ s : CollisionState, Good s → ∃ s' : CollisionState, nextIter? n s = some s' ∧ Good s' := by
  intro n
  induction n with
  | zero =>
    intro s hs
    exact ⟨s, rfl, hs⟩
  | succ n ih =>
    intro s hs
    rcases ih s hs with ⟨mid, hmid, hmidGood⟩
    rcases next?_eq_some_of_good mid hmidGood with ⟨s', hs'⟩
    refine ⟨s', ?_, ?_⟩
    · simp [nextIter?, hmid, hs']
    · exact hgoodClosed hmidGood hs'

theorem PaperLink.semiconj_iter {m : ℕ} {next : Fin m → Bool → Fin m × Bool × ℤ}
    (link : PaperLink m next)
    (hgoodClosed : ∀ {a a' : CollisionState}, Good a → next? a = some a' → Good a') :
    ∀ n : Nat, ∀ s : CollisionState, Good s →
      Option.map link.encode (nextIter? n s) = iter? (paperFctrl? next) n (link.encode s) := by
  intro n
  induction n with
  | zero =>
    intro s _hs
    simp [nextIter?, iter?]
  | succ n ih =>
    intro s hs
    rcases nextIter?_exists_good (hgoodClosed := hgoodClosed) n s hs with ⟨mid, hmid, hmidGood⟩
    have hiter : iter? (paperFctrl? next) n (link.encode s) = some (link.encode mid) := by
      -- Use IH and the concrete witness `hmid`.
      have hih : Option.map link.encode (nextIter? n s) = iter? (paperFctrl? next) n (link.encode s) :=
        ih s hs
      -- Rewrite the LHS using `hmid`.
      have hih' := hih
      simp [hmid] at hih'
      exact hih'.symm
    -- One more step: reduce both sides to the one-step semiconjugacy at `mid`.
    calc
      Option.map link.encode (nextIter? (n + 1) s) =
          Option.map link.encode (next? mid) := by
            simp [nextIter?, hmid]
      _ = paperFctrl? next (link.encode mid) := link.semiconj mid hmidGood
      _ = iter? (paperFctrl? next) (n + 1) (link.encode s) := by
            simp [iter?, hiter]

end UnitSquareMap

end Billiards
end MirandaDynamics
end HeytingLean
