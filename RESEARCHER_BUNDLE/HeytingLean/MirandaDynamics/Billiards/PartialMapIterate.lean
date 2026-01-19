import Mathlib.Tactic

/-!
# MirandaDynamics.Billiards: iteration and return for partial deterministic maps

Many WS7 statements are naturally phrased for partial deterministic dynamics `f : α → Option α`.

This file provides:
- `iter? f n a` : `n`-step iteration (fails if any intermediate step is undefined),
- a semiconjugacy lemma transporting `iter?` along `Option.map`,
- a noncomputable “first return” operator to a section predicate `S : α → Prop`.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

universe u v

/-- Iterate a partial map `f : α → Option α` `n` times (fails if any intermediate step is `none`). -/
def iter? {α : Type u} (f : α → Option α) : Nat → α → Option α
  | 0, a => some a
  | n + 1, a =>
      match iter? f n a with
      | none => none
      | some b => f b

@[simp] theorem iter?_zero {α : Type u} (f : α → Option α) (a : α) : iter? f 0 a = some a := rfl

@[simp] theorem iter?_succ {α : Type u} (f : α → Option α) (n : Nat) (a : α) :
    iter? f (n + 1) a =
      match iter? f n a with
      | none => none
      | some b => f b :=
  rfl

theorem iter?_succ' {α : Type u} (f : α → Option α) (n : Nat) (a : α) :
    iter? f (n + 1) a = (iter? f n a).bind f := by
  cases h : iter? f n a <;> simp [iter?, h, Option.bind]

/-- Transport an `Option`-semiconjugacy along `iter?`. -/
theorem iter?_map_semiconj {α : Type u} {β : Type v} (f : α → Option α) (g : β → Option β)
    (encode : α → β)
    (hstep : ∀ a : α, Option.map encode (f a) = g (encode a)) :
    ∀ n : Nat, ∀ a : α, Option.map encode (iter? f n a) = iter? g n (encode a) := by
  intro n
  induction n with
  | zero =>
    intro a
    simp [iter?]
  | succ n ih =>
    intro a
    -- Expand both sides one step and use IH plus the one-step hypothesis.
    cases h : iter? f n a with
    | none =>
      have hn' : iter? g n (encode a) = none := by
        simpa [h] using (ih a).symm
      simp [iter?, h, hn']
    | some b =>
      have hb : Option.map encode (iter? f n a) = some (encode b) := by
        simp [h]
      -- Use IH to rewrite the intermediate iterate on the RHS.
      have : iter? g n (encode a) = some (encode b) := by
        -- Compare `hb` with IH.
        have hb' : Option.map encode (iter? f n a) = iter? g n (encode a) := ih a
        simpa [hb] using hb'.symm
      -- Now both sides reduce to the one-step semiconjugacy at `b`.
      simp [iter?, h, this, hstep b]

/-! ## Return relations -/

/-- A choice-free “return” relation: `b` is hit in positive time and lies in the section `S`. -/
def ReturnRel {α : Type u} (f : α → Option α) (S : α → Prop) (a b : α) : Prop :=
  ∃ n : Nat, iter? f (n + 1) a = some b ∧ S b

theorem ReturnRel.map {α : Type u} {β : Type v} (f : α → Option α) (g : β → Option β)
    (encode : α → β) (S : α → Prop) (T : β → Prop)
    (hstep : ∀ a : α, Option.map encode (f a) = g (encode a))
    (hST : ∀ b : α, S b → T (encode b)) :
    ∀ {a b : α}, ReturnRel f S a b → ReturnRel g T (encode a) (encode b) := by
  intro a b hret
  rcases hret with ⟨n, hn, hSb⟩
  refine ⟨n, ?_, hST b hSb⟩
  have hiter := iter?_map_semiconj (f := f) (g := g) (encode := encode) hstep (n + 1) a
  -- Rewrite the semiconjugacy on the concrete iterate.
  have hn' :
      (match iter? f n a with
        | none => none
        | some b0 => f b0) = some b := by
    simpa [iter?] using hn
  have : (some (encode b) : Option β) = iter? g (n + 1) (encode a) := by
    simpa [hn'] using hiter
  exact this.symm

/-- A (noncomputable) “return” to a section predicate `S`.

If there exists some positive iterate landing in `S`, choose one such landing point and return it.
(No minimality/“first hit” is claimed here; that refinement requires additional decidability or
structure.) -/
noncomputable def return? {α : Type u} (f : α → Option α) (S : α → Prop) (a : α) : Option α := by
  classical
  exact
    if h : ∃ n : Nat, ∃ b : α, iter? f (n + 1) a = some b ∧ S b then
      some (Classical.choose (Classical.choose_spec h))
    else
      none

theorem return?_spec {α : Type u} (f : α → Option α) (S : α → Prop) (a b : α)
    (h : return? f S a = some b) :
    ∃ n : Nat, iter? f (n + 1) a = some b ∧ S b := by
  classical
  unfold return? at h
  by_cases hex : ∃ n : Nat, ∃ b : α, iter? f (n + 1) a = some b ∧ S b
  · -- Unpack the nested `Classical.choose` witnesses.
    have h' := h
    -- Reduce the dependent `if` using the witness `hex`.
    rw [dif_pos hex] at h'
    refine ⟨Classical.choose hex, ?_⟩
    have hb' : Classical.choose (Classical.choose_spec hex) = b :=
      Option.some.inj h'
    have hspec : iter? f (Classical.choose hex + 1) a =
        some (Classical.choose (Classical.choose_spec hex)) ∧ S (Classical.choose (Classical.choose_spec hex)) :=
      Classical.choose_spec (Classical.choose_spec hex)
    simpa [hb'] using hspec
  · have h' := h
    rw [dif_neg hex] at h'
    cases h'

theorem return?_mem {α : Type u} (f : α → Option α) (S : α → Prop) (a b : α)
    (h : return? f S a = some b) : S b := by
  rcases return?_spec (f := f) (S := S) (a := a) (b := b) h with ⟨n, _hn, hb⟩
  exact hb

end Billiards
end MirandaDynamics
end HeytingLean
