import HeytingLean.MirandaDynamics.Computation.GeneralizedShift

/-!
# MirandaDynamics.Computation: generalized shifts with finite control (WS5+ next step)

`Computation/GeneralizedShift.lean` defines a “control-free” generalized shift whose local rule
depends only on the head symbol.

For connecting to paper/physics realizations, it is often convenient to separate:
* a **finite control state** `q`, and
* the bi-infinite tape contents `t : Int → α`.

This file defines the corresponding controlled generalized shift and its one-step update.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Computation

universe u

structure GenShiftCtrlRule (Q : Type u) (α : Type u) where
  /-- Local update: given control state `q` and head symbol `a`, produce updated control state,
  updated symbol, and a head move `dh`. -/
  next : Q → α → Q × α × Int

structure GenShiftCtrlCfg (Q : Type u) (α : Type u) where
  state : Q
  tape : Tape α
  head : Int

namespace GenShiftCtrlCfg

@[ext] theorem ext {Q α : Type u} {c₁ c₂ : GenShiftCtrlCfg Q α}
    (hq : c₁.state = c₂.state) (ht : c₁.tape = c₂.tape) (hh : c₁.head = c₂.head) :
    c₁ = c₂ := by
  cases c₁
  cases c₂
  cases hq
  cases ht
  cases hh
  rfl

end GenShiftCtrlCfg

namespace GenShiftCtrlRule

variable {Q α : Type u}

noncomputable def step (r : GenShiftCtrlRule Q α) (cfg : GenShiftCtrlCfg Q α) : GenShiftCtrlCfg Q α :=
  let a := cfg.tape cfg.head
  let out := r.next cfg.state a
  let q' := out.1
  let a' := out.2.1
  let dh := out.2.2
  { state := q'
    tape := tapeUpdate cfg.tape cfg.head a'
    head := cfg.head + dh }

end GenShiftCtrlRule

noncomputable def genShiftCtrlDetSys {Q α : Type u} (r : GenShiftCtrlRule Q α) : DetSys (GenShiftCtrlCfg Q α) :=
  ⟨GenShiftCtrlRule.step r⟩

noncomputable def genShiftCtrlHaltSys {Q α : Type u} (r : GenShiftCtrlRule Q α) (halts : GenShiftCtrlCfg Q α → Prop) :
    HaltSys (GenShiftCtrlCfg Q α) :=
  { step := GenShiftCtrlRule.step r
    halts := halts }

/-! ## Simulation: embed a `HaltSys` as a controlled generalized shift -/

namespace ControlledEmbed

variable {Cfg : Type u} (M : HaltSys Cfg)

/-- A trivial tape carrying no information: everything is stored in the control state. -/
def embedTape : Tape PUnit :=
  fun _ => PUnit.unit

/-- Embed a halting-system configuration as a controlled generalized-shift configuration. -/
def embedCfg (c : Cfg) : GenShiftCtrlCfg Cfg PUnit :=
  { state := c
    tape := embedTape
    head := 0 }

/-- Controlled shift rule: update the control state by `M.step`, keep the tape, and do not move. -/
def rule : GenShiftCtrlRule Cfg PUnit where
  next q _ := (M.step q, PUnit.unit, 0)

/-- Halting predicate restricted to the embedded image. -/
def haltsCfg : GenShiftCtrlCfg Cfg PUnit → Prop :=
  fun cfg => ∃ c : Cfg, cfg = embedCfg c ∧ M.halts c

/-- The induced controlled generalized-shift halting system. -/
noncomputable def sys : HaltSys (GenShiftCtrlCfg Cfg PUnit) :=
  genShiftCtrlHaltSys (r := rule M) (halts := haltsCfg M)

def Rel (_M : HaltSys Cfg) (c : Cfg) (cfg : GenShiftCtrlCfg Cfg PUnit) : Prop :=
  cfg = embedCfg c

theorem step_embedCfg (c : Cfg) :
    GenShiftCtrlRule.step (rule M) (embedCfg c) = embedCfg (M.step c) := by
  classical
  apply GenShiftCtrlCfg.ext
  · rfl
  · -- Tape is unchanged: updating a `PUnit` tape does nothing.
    funext z
    simp [GenShiftCtrlRule.step, rule, embedCfg, tapeUpdate]
  · simp [GenShiftCtrlRule.step, rule, embedCfg]

theorem sim_step {c : Cfg} {cfg : GenShiftCtrlCfg Cfg PUnit} (h : Rel M c cfg) :
    Rel M (M.step c) (GenShiftCtrlRule.step (rule M) cfg) := by
  cases h
  simpa [Rel] using step_embedCfg (M := M) c

theorem sim_halts {c : Cfg} {cfg : GenShiftCtrlCfg Cfg PUnit} (h : Rel M c cfg) :
    (M.halts c ↔ (sys M).halts cfg) := by
  cases h
  constructor
  · intro hc
    exact ⟨c, rfl, hc⟩
  · rintro ⟨c', hc', hc'Halts⟩
    have hstate : c = c' := by
      -- Both are the control state at `head=0` with the same `PUnit` tape.
      simpa [embedCfg] using congrArg GenShiftCtrlCfg.state hc'
    cases hstate
    simpa using hc'Halts

end ControlledEmbed

end Computation
end MirandaDynamics
end HeytingLean
