import HeytingLean.MirandaDynamics.Billiards.PartialMapIterate
import HeytingLean.MirandaDynamics.Billiards.PaperTargetDomain

/-!
# MirandaDynamics.Billiards: generic semiconjugacy interface to the WS7.4 paper map

`GeometryToPaperTarget.lean` specializes the WS7.3→WS7.4 semiconjugacy interface to the unit-square
map. For the long-horizon “real paper billiard” construction, we want the same scaffolding but
*independent* of any specific billiard table.

This file provides a generic `PaperLink` record for any collision cross-section type `α`, together
with iteration transport via `iter?_map_semiconj`.

It does **not** solve the remaining geometry gap (constructing a real billiard `α` + `next?`), but
it makes the target statement reusable once that geometry is supplied.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set

structure PaperLink (α : Type) (m : ℕ) (next : Fin m → Bool → Fin m × Bool × ℤ) where
  /-- Cross-section “good set” excluding singularities. -/
  Good : α → Prop
  /-- Deterministic (partial) next-collision map on the cross-section. -/
  next? : α → Option α
  /-- Coding into the paper target coordinate plane. -/
  encode : α → ℝ × ℝ
  /-- On good states, the code lands in the branch domain. -/
  encode_mem : ∀ s : α, Good s → encode s ∈ CtrlDomain m
  /-- One-step semiconjugacy to the WS7.4 target map. -/
  semiconj : ∀ s : α, Good s → Option.map encode (next? s) = paperFctrl? next (encode s)

namespace PaperLink

variable {α : Type} {m : ℕ} {next : Fin m → Bool → Fin m × Bool × ℤ}

theorem good_of_iter?_eq_some (link : PaperLink α m next)
    (hgoodClosed : ∀ {a a' : α}, link.Good a → link.next? a = some a' → link.Good a') :
    ∀ n : Nat, ∀ s s' : α, link.Good s → iter? link.next? n s = some s' → link.Good s' := by
  intro n
  induction n with
  | zero =>
    intro s s' hs hiter
    simpa [iter?] using (Option.some.inj hiter ▸ hs)
  | succ n ih =>
    intro s s' hs hiter
    -- Expand one step of `iter?`.
    simp [iter?] at hiter
    cases hmid : iter? link.next? n s with
    | none =>
      simp [hmid] at hiter
    | some mid =>
      -- `mid` is good by the IH, and the final step preserves goodness.
      have hmidGood : link.Good mid := ih s mid hs hmid
      exact hgoodClosed hmidGood hiter

theorem semiconj_iter (link : PaperLink α m next)
    (hgoodClosed : ∀ {a a' : α}, link.Good a → link.next? a = some a' → link.Good a') :
    ∀ n : Nat, ∀ s : α, link.Good s →
      Option.map link.encode (iter? link.next? n s) = iter? (paperFctrl? next) n (link.encode s) := by
  intro n
  induction n with
  | zero =>
    intro s _hs
    simp [iter?]
  | succ n ih =>
    intro s hs
    -- Split on whether the intermediate iterate is defined.
    cases hmid : iter? link.next? n s with
    | none =>
      have : iter? (paperFctrl? next) n (link.encode s) = none := by
        -- If the LHS is `none`, the IH forces the RHS to be `none`.
        have h := ih s hs
        simpa [hmid] using h.symm
      simp [iter?, hmid, this]
    | some mid =>
      have hmidGood : link.Good mid :=
        good_of_iter?_eq_some (link := link) (hgoodClosed := hgoodClosed) n s mid hs hmid
      -- Use the IH at `s` and then the one-step semiconjugacy at `mid`.
      have hiter : iter? (paperFctrl? next) n (link.encode s) = some (link.encode mid) := by
        have h := ih s hs
        simpa [hmid] using h.symm
      calc
        Option.map link.encode (iter? link.next? (n + 1) s)
            = Option.map link.encode (link.next? mid) := by
                simp [iter?, hmid]
        _ = paperFctrl? next (link.encode mid) := link.semiconj mid hmidGood
        _ = iter? (paperFctrl? next) (n + 1) (link.encode s) := by
              simp [iter?, hiter]

end PaperLink

end Billiards
end MirandaDynamics
end HeytingLean
