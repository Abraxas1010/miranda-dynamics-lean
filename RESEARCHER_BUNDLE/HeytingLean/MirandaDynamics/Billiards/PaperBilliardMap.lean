import HeytingLean.MirandaDynamics.Billiards.PaperTargetDomain
import HeytingLean.MirandaDynamics.Billiards.PartialMapIterate

/-!
# MirandaDynamics.Billiards: a “paper billiard” cross-section map (non-geometric model)

This file provides a concrete *cross-section dynamics* model whose state space is already the
WS7.4 coordinate plane `ℝ×ℝ`.

It is **not** yet the geometric billiard table from the paper (walls/corridors/parabolas). Rather,
it packages the exact `CollisionState`/`Good`/`encode`/`semiconj` interface that the *real* billiard
construction must satisfy, and proves the `PaperLink.semiconj` theorem by definition.

This lets the return-map lifting theorems be stated and used now, while the geometric realization
remains a long-horizon task.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set

namespace PaperBilliardMap

variable {m : ℕ} (next : Fin m → Bool → Fin m × Bool × ℤ)

/-- Cross-section “collision state”: a point in the WS7.4 branch domain. -/
structure CollisionState (m : ℕ) where
  pos : ℝ × ℝ
  pos_mem : pos ∈ CtrlDomain m

/-- In this cross-section model, every state is “good”. (Singularities belong to the geometric layer.) -/
def Good {m : ℕ} (_s : CollisionState m) : Prop := True

/-- The one-step “next collision” map is simply the WS7.4 paper map. -/
def next? {m : ℕ} (next : Fin m → Bool → Fin m × Bool × ℤ) (s : CollisionState m) :
    Option (CollisionState m) :=
  match h : paperFctrl? next s.pos with
  | none => none
  | some p' =>
      some
        { pos := p'
          pos_mem := mem_CtrlDomain_of_paperFctrl?_eq_some (m := m) (next := next) (p := s.pos) (p' := p') h }

/-- The canonical encoding is the identity on positions. -/
def encode {m : ℕ} (s : CollisionState m) : ℝ × ℝ := s.pos

@[simp] theorem encode_def {m : ℕ} (s : CollisionState m) : encode s = s.pos := rfl

theorem semiconj {m : ℕ} (next : Fin m → Bool → Fin m × Bool × ℤ) (s : CollisionState m) :
    Option.map (encode (m := m)) (next? (m := m) next s) = paperFctrl? next (encode s) := by
  -- By definition, `next?` is `paperFctrl?` lifted to the subtype `CtrlDomain`.
  classical
  cases h : paperFctrl? next s.pos with
  | none =>
      simp [next?, encode, h]
  | some p' =>
      simp [next?, encode, h]

/-! ## A `PaperLink` instance compatible with the WS7.3 scaffolding -/

structure PaperLink (m : ℕ) (next : Fin m → Bool → Fin m × Bool × ℤ) where
  encode : CollisionState m → ℝ × ℝ
  encode_mem : ∀ s, Good s → encode s ∈ CtrlDomain m
  semiconj : ∀ s, Good s → Option.map encode (next? next s) = paperFctrl? next (encode s)

def paperLink (m : ℕ) (next : Fin m → Bool → Fin m × Bool × ℤ) : PaperLink m next :=
  { encode := encode (m := m)
    encode_mem := by
      intro s _hs
      simpa [encode] using s.pos_mem
    semiconj := by
      intro s _hs
      simpa [encode] using semiconj (m := m) (next := next) s }

/-! ## Iteration and return lifting (immediate in this model) -/

theorem semiconj_iter {m : ℕ} (next : Fin m → Bool → Fin m × Bool × ℤ) :
    ∀ n : Nat, ∀ s : CollisionState m,
      Option.map (encode (m := m)) (iter? (next? next) n s) =
        iter? (paperFctrl? next) n (encode s) := by
  intro n s
  exact iter?_map_semiconj (f := next? next) (g := paperFctrl? next) (encode := encode (m := m))
    (hstep := fun a => semiconj (m := m) (next := next) a) n s

end PaperBilliardMap

end Billiards
end MirandaDynamics
end HeytingLean
