import Mathlib.Order.WellFounded
import HeytingLean.MirandaDynamics.TKFT.BordismSemantics

/-!
# MirandaDynamics.TKFT: a discrete bordism model (state machine + terminal output)

This file provides a fully mechanized **discrete** model of a “dynamical bordism”:

- a (deterministic) state machine `step : State → State`,
- a way to initialize from an input boundary `init : In → State`,
- a terminal output observation `done : State → Option Out`,
- an axiom-free invariant `done_step` saying that once an output appears, it stays the same along
  future steps.

We then define the induced reaching relation and show that the *gluing* construction on these
discrete bordisms corresponds to relational composition of their reaching semantics.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace TKFT

universe u v w

/-- A discrete “dynamical bordism” from `In` to `Out`. -/
structure DiscreteBordism.{uIn, uOut, uState} (In : Type uIn) (Out : Type uOut) :
    Type (max (uIn + 1) (uOut + 1) (uState + 1)) where
  State : Type uState
  step : State → State
  init : In → State
  done : State → Option Out
  /-- Terminality: once `done` returns an output, it stays that output along one step. -/
  done_step : ∀ s b, done s = some b → done (step s) = some b

namespace DiscreteBordism

variable {In : Type u} {Mid : Type v} {Out : Type w}

/-- The reaching relation induced by a discrete bordism: an output is reachable if it appears as a
terminal observation at some finite time. -/
def reachingRel (B : DiscreteBordism In Out) : ReachingRel In Out :=
  ⟨fun a b => ∃ t : Nat, B.done (B.step^[t] (B.init a)) = some b⟩

@[simp] theorem reachingRel_rel (B : DiscreteBordism In Out) (a : In) (b : Out) :
    (B.reachingRel).rel a b ↔ ∃ t : Nat, B.done (B.step^[t] (B.init a)) = some b :=
  Iff.rfl

theorem done_iter_of_done (B : DiscreteBordism In Out) (s : B.State) (b : Out) (n : Nat)
    (h : B.done s = some b) : B.done (B.step^[n] s) = some b := by
  induction n with
  | zero =>
    simpa using h
  | succ n ih =>
    simpa [Function.iterate_succ_apply'] using B.done_step _ _ ih

theorem reachingRel_functional (B : DiscreteBordism In Out) : (B.reachingRel).Functional := by
  intro a b₁ b₂ hb₁ hb₂
  rcases hb₁ with ⟨t₁, ht₁⟩
  rcases hb₂ with ⟨t₂, ht₂⟩
  by_cases hle : t₁ ≤ t₂
  · have ht₁' : B.done (B.step^[t₂] (B.init a)) = some b₁ := by
      -- propagate `done = some b₁` from time `t₁` to time `t₂`
      have hprop :
          B.done (B.step^[t₂ - t₁] (B.step^[t₁] (B.init a))) = some b₁ :=
        B.done_iter_of_done (s := B.step^[t₁] (B.init a)) (b := b₁) (n := t₂ - t₁) ht₁
      -- rewrite the iterate state to `step^[t₂] (init a)` using `iterate_add_apply`
      have hIter :
          B.step^[t₂ - t₁ + t₁] (B.init a) = B.step^[t₂ - t₁] (B.step^[t₁] (B.init a)) := by
        simpa using (Function.iterate_add_apply (f := B.step) (t₂ - t₁) t₁ (B.init a))
      have hNat : t₂ - t₁ + t₁ = t₂ := Nat.sub_add_cancel hle
      have : B.done (B.step^[t₂ - t₁ + t₁] (B.init a)) = some b₁ := by
        simpa [hIter] using hprop
      simpa [hNat] using this
    exact Option.some.inj (ht₁'.symm.trans ht₂)
  · -- symmetric case
    have hle' : t₂ ≤ t₁ := le_of_not_ge hle
    have ht₂' : B.done (B.step^[t₁] (B.init a)) = some b₂ := by
      have hprop :
          B.done (B.step^[t₁ - t₂] (B.step^[t₂] (B.init a))) = some b₂ :=
        B.done_iter_of_done (s := B.step^[t₂] (B.init a)) (b := b₂) (n := t₁ - t₂) ht₂
      have hIter :
          B.step^[t₁ - t₂ + t₂] (B.init a) = B.step^[t₁ - t₂] (B.step^[t₂] (B.init a)) := by
        simpa using (Function.iterate_add_apply (f := B.step) (t₁ - t₂) t₂ (B.init a))
      have hNat : t₁ - t₂ + t₂ = t₁ := Nat.sub_add_cancel hle'
      have : B.done (B.step^[t₁ - t₂ + t₂] (B.init a)) = some b₂ := by
        simpa [hIter] using hprop
      simpa [hNat] using this
    exact (Option.some.inj (ht₂'.symm.trans ht₁)).symm

/-- Forget a discrete bordism to a semantics-only bordism. -/
def semantics (B : DiscreteBordism In Out) : BordismSemantics In Out :=
  ⟨B.reachingRel⟩

@[simp] theorem semantics_reach (B : DiscreteBordism In Out) : B.semantics.reach = B.reachingRel :=
  rfl

/-- Gluing of discrete bordisms: run the first machine until it produces an output `m : Mid`,
then feed `m` as the input to the second machine. -/
def glue (B₁ : DiscreteBordism In Mid) (B₂ : DiscreteBordism Mid Out) : DiscreteBordism In Out where
  State := Sum B₁.State B₂.State
  init a := Sum.inl (B₁.init a)
  step
    | Sum.inl s₁ =>
      match B₁.done s₁ with
      | some m => Sum.inr (B₂.init m)
      | none => Sum.inl (B₁.step s₁)
    | Sum.inr s₂ => Sum.inr (B₂.step s₂)
  done
    | Sum.inl _ => none
    | Sum.inr s₂ => B₂.done s₂
  done_step := by
    intro s b h
    cases s with
    | inl s₁ =>
      cases h
    | inr s₂ =>
      -- `done` is `B₂.done` on the right component.
      simpa using B₂.done_step s₂ b h

section GlueLemmas

variable (B₁ : DiscreteBordism In Mid) (B₂ : DiscreteBordism Mid Out)

@[simp] theorem glue_init (a : In) : (glue B₁ B₂).init a = Sum.inl (B₁.init a) := rfl

@[simp] theorem glue_done_inl (s₁ : B₁.State) : (glue B₁ B₂).done (Sum.inl s₁) = none := rfl

@[simp] theorem glue_done_inr (s₂ : B₂.State) : (glue B₁ B₂).done (Sum.inr s₂) = B₂.done s₂ := rfl

@[simp] theorem glue_step_inr (s₂ : B₂.State) :
    (glue B₁ B₂).step (Sum.inr s₂) = Sum.inr (B₂.step s₂) :=
  rfl

theorem glue_step_inl_none (s₁ : B₁.State) (h : B₁.done s₁ = none) :
    (glue B₁ B₂).step (Sum.inl s₁) = Sum.inl (B₁.step s₁) := by
  simp [glue, h]

theorem glue_step_inl_some (s₁ : B₁.State) (m : Mid) (h : B₁.done s₁ = some m) :
    (glue B₁ B₂).step (Sum.inl s₁) = Sum.inr (B₂.init m) := by
  simp [glue, h]

theorem glue_iter_inr (s₂ : B₂.State) :
    ∀ n : Nat, (glue B₁ B₂).step^[n] (Sum.inr s₂) = Sum.inr (B₂.step^[n] s₂) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [Function.iterate_succ_apply', ih]

theorem glue_iter_inl_of_no_done (a : In) :
    ∀ n : Nat,
      (∀ i < n, B₁.done (B₁.step^[i] (B₁.init a)) = none) →
        (glue B₁ B₂).step^[n] (Sum.inl (B₁.init a)) = Sum.inl (B₁.step^[n] (B₁.init a)) := by
  intro n
  induction n with
  | zero =>
    intro _
    rfl
  | succ n ih =>
    intro hNo
    have hNo' : ∀ i < n, B₁.done (B₁.step^[i] (B₁.init a)) = none :=
      fun i hi => hNo i (Nat.lt_succ_of_lt hi)
    have hDone : B₁.done (B₁.step^[n] (B₁.init a)) = none :=
      hNo n (Nat.lt_succ_self n)
    have hAt :
        (glue B₁ B₂).step^[n] (Sum.inl (B₁.init a)) = Sum.inl (B₁.step^[n] (B₁.init a)) :=
      ih hNo'
    calc
      (glue B₁ B₂).step^[n + 1] (Sum.inl (B₁.init a))
          = (glue B₁ B₂).step ((glue B₁ B₂).step^[n] (Sum.inl (B₁.init a))) := by
              simp [Function.iterate_succ_apply']
      _ = (glue B₁ B₂).step (Sum.inl (B₁.step^[n] (B₁.init a))) := by
        simp [hAt]
      _ = Sum.inl (B₁.step (B₁.step^[n] (B₁.init a))) := by
        simpa using (glue_step_inl_none (B₁ := B₁) (B₂ := B₂) (s₁ := B₁.step^[n] (B₁.init a)) hDone)
      _ = Sum.inl (B₁.step^[n + 1] (B₁.init a)) := by
        simp [Function.iterate_succ_apply']

end GlueLemmas

/-- The reaching semantics of `glue` is relational composition. -/
theorem reachingRel_glue_eq_comp (B₁ : DiscreteBordism In Mid) (B₂ : DiscreteBordism Mid Out) :
    (glue B₁ B₂).reachingRel = ReachingRel.comp B₁.reachingRel B₂.reachingRel := by
  classical
  ext a c
  constructor
  · -- glue → comp: pick the first time the glued machine enters the right component
    rintro ⟨t, ht⟩
    let stateAt : Nat → (glue B₁ B₂).State :=
      fun n => (glue B₁ B₂).step^[n] ((glue B₁ B₂).init a)
    let Q : Nat → Prop := fun n => ∃ s₂ : B₂.State, stateAt n = Sum.inr s₂

    have hQt : Q t := by
      have htAt : (glue B₁ B₂).done (stateAt t) = some c := by
        simpa [stateAt] using ht
      cases hst : stateAt t with
      | inl s₁ =>
        exfalso
        have htAt' := htAt
        simp [hst, glue] at htAt'
      | inr s₂ =>
        exact ⟨s₂, hst⟩

    let S : Set Nat := {n | Q n}
    have hS : S.Nonempty := ⟨t, hQt⟩
    let wf : WellFounded (fun m n : Nat => m < n) := Nat.lt_wfRel.wf
    let t₀ : Nat := wf.min S hS

    have ht₀Q : Q t₀ := by
      have : t₀ ∈ S := wf.min_mem S hS
      exact this

    have hNotQ_lt : ∀ n < t₀, ¬Q n := by
      intro n hn hQn
      have : ¬ n < t₀ := wf.not_lt_min S hS (x := n) hQn
      exact this hn

    have hNotQ0 : ¬Q 0 := by
      intro hQ0
      rcases hQ0 with ⟨s₂, hs₂⟩
      -- but time 0 is `inl _`
      simp [stateAt, glue] at hs₂

    have ht₀ne : t₀ ≠ 0 := by
      intro h0
      apply hNotQ0
      simpa [h0] using ht₀Q

    obtain ⟨k, hk⟩ : ∃ k, t₀ = k + 1 :=
      Nat.exists_eq_succ_of_ne_zero ht₀ne

    have hStateAt :
        ∀ n : Nat, n ≤ k → stateAt n = Sum.inl (B₁.step^[n] (B₁.init a)) := by
      intro n hn
      induction n with
      | zero =>
        simp [stateAt, glue]
      | succ n ih =>
        have hn' : n ≤ k := Nat.le_trans (Nat.le_succ n) hn
        have hPrev : stateAt n = Sum.inl (B₁.step^[n] (B₁.init a)) := ih hn'
        have hn1_lt : n + 1 < t₀ := by
          have : n + 1 < k + 1 := Nat.lt_succ_of_le hn
          simpa [hk] using this
        have hNotQSucc : ¬Q (n + 1) := hNotQ_lt (n + 1) hn1_lt
        have hStep : stateAt (n + 1) = (glue B₁ B₂).step (stateAt n) := by
          simp [stateAt, Function.iterate_succ_apply']
        -- `done` must be `none`, otherwise we'd jump right and contradict `hNotQSucc`.
        have hDone : B₁.done (B₁.step^[n] (B₁.init a)) = none := by
          cases hD : B₁.done (B₁.step^[n] (B₁.init a)) with
          | none => rfl
          | some m =>
            exfalso
            apply hNotQSucc
            refine ⟨B₂.init m, ?_⟩
            -- compute the (n+1)-state
            simp [hStep, hPrev, glue_step_inl_some (B₁ := B₁) (B₂ := B₂)
              (s₁ := B₁.step^[n] (B₁.init a)) (m := m) hD]
        -- advance one step on the left
        have hNext :
            stateAt (n + 1) = Sum.inl (B₁.step (B₁.step^[n] (B₁.init a))) := by
          simpa [hStep, hPrev] using
            (glue_step_inl_none (B₁ := B₁) (B₂ := B₂) (s₁ := B₁.step^[n] (B₁.init a)) hDone)
        simpa [Function.iterate_succ_apply'] using hNext

    have hAtK : stateAt k = Sum.inl (B₁.step^[k] (B₁.init a)) :=
      hStateAt k (le_rfl)
    have hAtK1 : ∃ s₂₀ : B₂.State, stateAt (k + 1) = Sum.inr s₂₀ := by
      -- `t₀ = k+1` and `Q t₀`
      rcases ht₀Q with ⟨s₂₀, hs₂₀⟩
      refine ⟨s₂₀, ?_⟩
      simpa [t₀, hk, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hs₂₀
    rcases hAtK1 with ⟨s₂₀, hs₂₀⟩

    have hStepK : stateAt (k + 1) = (glue B₁ B₂).step (stateAt k) := by
      simp [stateAt, Function.iterate_succ_apply']

    have hHandoff :
        ∃ m : Mid, B₁.done (B₁.step^[k] (B₁.init a)) = some m ∧ s₂₀ = B₂.init m := by
      have hStep' :
          (glue B₁ B₂).step (Sum.inl (B₁.step^[k] (B₁.init a))) = Sum.inr s₂₀ := by
        simpa [hStepK, hAtK] using hs₂₀
      let o := B₁.done (B₁.step^[k] (B₁.init a))
      cases hO : o with
      | none =>
        exfalso
        have hDone : B₁.done (B₁.step^[k] (B₁.init a)) = none := by
          simpa [o] using hO
        -- would remain on the left
        have hStepNone :
            (glue B₁ B₂).step (Sum.inl (B₁.step^[k] (B₁.init a))) =
              Sum.inl (B₁.step (B₁.step^[k] (B₁.init a))) :=
          glue_step_inl_none (B₁ := B₁) (B₂ := B₂) (s₁ := B₁.step^[k] (B₁.init a)) hDone
        have hEq := hStep'
        -- rewrite the LHS using the computed step
        simp [hStepNone] at hEq
      | some m =>
        have hDone : B₁.done (B₁.step^[k] (B₁.init a)) = some m := by
          simpa [o] using hO
        have hStepSome :
            (glue B₁ B₂).step (Sum.inl (B₁.step^[k] (B₁.init a))) = Sum.inr (B₂.init m) :=
          glue_step_inl_some (B₁ := B₁) (B₂ := B₂) (s₁ := B₁.step^[k] (B₁.init a)) (m := m) hDone
        have hSum : (Sum.inr s₂₀ : (glue B₁ B₂).State) = Sum.inr (B₂.init m) :=
          hStep'.symm.trans hStepSome
        have hs : s₂₀ = B₂.init m :=
          Sum.inr.inj hSum
        exact ⟨m, ⟨hDone, hs⟩⟩

    rcases hHandoff with ⟨m, hmDone, hs₂₀eq⟩
    have hReach₁ : (B₁.reachingRel).rel a m := ⟨k, hmDone⟩

    have ht₀_le_t : t₀ ≤ t := by
      -- by minimality of `t₀` in the set `S`
      have : ¬ t < t₀ := wf.not_lt_min S hS (x := t) hQt
      exact le_of_not_gt this

    let n : Nat := t - t₀
    have hNat : t₀ + n = t := Nat.add_sub_of_le ht₀_le_t
    have hAtT :
        stateAt t = (glue B₁ B₂).step^[n] (stateAt t₀) := by
      -- rewrite `t` as `n + t₀` and use `iterate_add_apply`
      have hNat' : n + t₀ = t := by simpa [Nat.add_comm] using hNat
      have : (glue B₁ B₂).step^[n + t₀] ((glue B₁ B₂).init a) =
          (glue B₁ B₂).step^[n] ((glue B₁ B₂).step^[t₀] ((glue B₁ B₂).init a)) := by
        simpa using (Function.iterate_add_apply (f := (glue B₁ B₂).step) n t₀ ((glue B₁ B₂).init a))
      -- unfold `stateAt`
      simpa [stateAt, hNat', this]

    have hAtT' : stateAt t = Sum.inr (B₂.step^[n] (B₂.init m)) := by
      have ht₀state : stateAt t₀ = Sum.inr (B₂.init m) := by
        -- `stateAt t₀ = stateAt (k+1) = inr s₂₀ = inr (init m)`
        have : stateAt t₀ = Sum.inr s₂₀ := by
          simpa [t₀, hk, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hs₂₀
        simpa [hs₂₀eq] using this
      simpa [hAtT, ht₀state] using
        glue_iter_inr (B₁ := B₁) (B₂ := B₂) (s₂ := B₂.init m) n

    have hReach₂ : (B₂.reachingRel).rel m c := by
      refine ⟨n, ?_⟩
      have : (glue B₁ B₂).done (stateAt t) = some c := by
        simpa [stateAt] using ht
      simpa [hAtT', glue] using this

    exact ⟨m, hReach₁, hReach₂⟩

  · -- comp → glue: use a minimal output time for `B₁` and then run `B₂`
    rintro ⟨m, hm, hc⟩
    let P : Nat → Prop := fun t => ∃ m : Mid, B₁.done (B₁.step^[t] (B₁.init a)) = some m
    have hP : ({t | P t} : Set Nat).Nonempty := by
      rcases hm with ⟨t, ht⟩
      exact ⟨t, ⟨m, ht⟩⟩
    let wf : WellFounded (fun m n : Nat => m < n) := Nat.lt_wfRel.wf
    let t₀ : Nat := wf.min ({t | P t} : Set Nat) hP
    have ht₀P : P t₀ := wf.min_mem ({t | P t} : Set Nat) hP
    let m₀ : Mid := Classical.choose ht₀P
    have hm₀ : B₁.done (B₁.step^[t₀] (B₁.init a)) = some m₀ := Classical.choose_spec ht₀P
    have hNoBefore : ∀ i < t₀, B₁.done (B₁.step^[i] (B₁.init a)) = none := by
      intro i hi
      have : ¬P i := by
        intro hPi
        have : ¬ i < t₀ := wf.not_lt_min ({t | P t} : Set Nat) hP (x := i) hPi
        exact this hi
      cases hDi : B₁.done (B₁.step^[i] (B₁.init a)) with
      | none => rfl
      | some mi =>
        exfalso
        exact this ⟨mi, hDi⟩
    have hmEq : m = m₀ := by
      have hFun := reachingRel_functional (In := In) (Out := Mid) B₁
      exact hFun a m m₀ hm ⟨t₀, hm₀⟩
    have hc' : (B₂.reachingRel).rel m₀ c := by
      simpa [hmEq] using hc
    rcases hc' with ⟨t₂, ht₂⟩
    refine ⟨t₀ + 1 + t₂, ?_⟩
    -- evolve `B₁` for `t₀` steps (no output earlier), then hand off to `B₂`
    have hAt₀ :
        (glue B₁ B₂).step^[t₀] (Sum.inl (B₁.init a)) = Sum.inl (B₁.step^[t₀] (B₁.init a)) :=
      glue_iter_inl_of_no_done (B₁ := B₁) (B₂ := B₂) a t₀ hNoBefore
    have hHandoff :
        (glue B₁ B₂).step (Sum.inl (B₁.step^[t₀] (B₁.init a))) = Sum.inr (B₂.init m₀) := by
      simpa using glue_step_inl_some (B₁ := B₁) (B₂ := B₂)
        (s₁ := B₁.step^[t₀] (B₁.init a)) (m := m₀) hm₀
    have hAt₀1 :
        (glue B₁ B₂).step^[t₀ + 1] (Sum.inl (B₁.init a)) = Sum.inr (B₂.init m₀) := by
      simp [Function.iterate_succ_apply', hAt₀, hHandoff]
    have hAtFinal :
        (glue B₁ B₂).step^[t₀ + 1 + t₂] (Sum.inl (B₁.init a)) =
          Sum.inr (B₂.step^[t₂] (B₂.init m₀)) := by
      -- run `t₀+1` steps to enter the right component, then `t₂` more steps there
      have hAdd : t₀ + 1 + t₂ = t₂ + (t₀ + 1) := by
        calc
          t₀ + 1 + t₂ = t₀ + (1 + t₂) := by simp [Nat.add_assoc]
          _ = t₀ + (t₂ + 1) := by simp [Nat.add_comm]
          _ = t₀ + t₂ + 1 := by simp [Nat.add_assoc]
          _ = t₂ + t₀ + 1 := by simp [Nat.add_left_comm, Nat.add_assoc]
          _ = t₂ + (t₀ + 1) := by simp [Nat.add_assoc]
      calc
        (glue B₁ B₂).step^[t₀ + 1 + t₂] (Sum.inl (B₁.init a))
            = (glue B₁ B₂).step^[t₂ + (t₀ + 1)] (Sum.inl (B₁.init a)) := by
                simp [hAdd]
        _ = (glue B₁ B₂).step^[t₂] ((glue B₁ B₂).step^[t₀ + 1] (Sum.inl (B₁.init a))) := by
              simpa using (Function.iterate_add_apply (f := (glue B₁ B₂).step) t₂ (t₀ + 1) (Sum.inl (B₁.init a)))
        _ = (glue B₁ B₂).step^[t₂] (Sum.inr (B₂.init m₀)) := by
              simp [hAt₀1]
        _ = Sum.inr (B₂.step^[t₂] (B₂.init m₀)) := by
              simpa using glue_iter_inr (B₁ := B₁) (B₂ := B₂) (s₂ := B₂.init m₀) t₂
    -- evaluate `done` at the final state
    have : (glue B₁ B₂).done (Sum.inr (B₂.step^[t₂] (B₂.init m₀))) = some c := by
      simpa [glue] using ht₂
    simpa [reachingRel, hAtFinal] using this

end DiscreteBordism

end TKFT
end MirandaDynamics
end HeytingLean
