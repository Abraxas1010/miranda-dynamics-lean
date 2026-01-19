import HeytingLean.MirandaDynamics.Computation.TuringMachine

/-!
# MirandaDynamics.Computation: generalized shifts (WS5+ mechanizable layer)

This file defines a minimal “generalized shift” on a bi-infinite tape indexed by `Int`, driven by a
local rule at a head position. It is packaged as a deterministic/halting system (`DetSys`/`HaltSys`)
from `Computation/TuringMachine.lean`.

It also provides a generic simulation embedding:

> every `HaltSys` can be simulated by a generalized shift on `Option Cfg`

This is a precise, fully mechanized stepping stone toward the Miranda billiards/fluids pipeline,
where symbolic dynamics (generalized shifts) are realized by physical flows.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Computation

universe u

abbrev Tape (α : Type u) : Type u :=
  Int → α

noncomputable def tapeUpdate {α : Type u} (t : Tape α) (i : Int) (a : α) : Tape α :=
  fun j => if j = i then a else t j

structure GenShiftRule (α : Type u) where
  /-- Local update: read the head symbol, write a new symbol, and move the head by `dh`. -/
  next : α → α × Int

structure GenShiftCfg (α : Type u) where
  tape : Tape α
  head : Int

namespace GenShiftCfg

@[ext] theorem ext {α : Type u} {c₁ c₂ : GenShiftCfg α} (ht : c₁.tape = c₂.tape) (hh : c₁.head = c₂.head) :
    c₁ = c₂ := by
  cases c₁
  cases c₂
  cases ht
  cases hh
  rfl

end GenShiftCfg

namespace GenShiftRule

variable {α : Type u}

noncomputable def step (r : GenShiftRule α) (cfg : GenShiftCfg α) : GenShiftCfg α :=
  let a := cfg.tape cfg.head
  let a' := (r.next a).1
  let dh := (r.next a).2
  { tape := tapeUpdate cfg.tape cfg.head a'
    head := cfg.head + dh }

end GenShiftRule

noncomputable def genShiftDetSys {α : Type u} (r : GenShiftRule α) : DetSys (GenShiftCfg α) :=
  ⟨GenShiftRule.step r⟩

noncomputable def genShiftHaltSys {α : Type u} (r : GenShiftRule α) (halts : GenShiftCfg α → Prop) :
    HaltSys (GenShiftCfg α) :=
  { step := GenShiftRule.step r
    halts := halts }

/-! ## Simulation: embed an arbitrary `HaltSys` into a generalized shift -/

namespace Embed

variable {Cfg : Type u} (M : HaltSys Cfg)

noncomputable def embedTape (c : Cfg) : Tape (Option Cfg) :=
  fun z => if z = 0 then some c else none

noncomputable def embedCfg (c : Cfg) : GenShiftCfg (Option Cfg) :=
  { tape := embedTape c
    head := 0 }

noncomputable def rule : GenShiftRule (Option Cfg) where
  next
    | none => (none, 0)
    | some c => (some (M.step c), 0)

noncomputable def haltsCfg : GenShiftCfg (Option Cfg) → Prop :=
  fun cfg => ∃ c : Cfg, cfg = embedCfg c ∧ M.halts c

noncomputable def sys : HaltSys (GenShiftCfg (Option Cfg)) :=
  genShiftHaltSys (r := rule M) (halts := haltsCfg M)

def Rel (_M : HaltSys Cfg) (c : Cfg) (cfg : GenShiftCfg (Option Cfg)) : Prop :=
  cfg = embedCfg c

theorem step_embedCfg (c : Cfg) :
    GenShiftRule.step (rule M) (embedCfg c) = embedCfg (M.step c) := by
  classical
  apply GenShiftCfg.ext
  · funext z
    by_cases hz : z = 0
    · subst hz
      simp [GenShiftRule.step, rule, embedCfg, embedTape, tapeUpdate]
    · have : (z : Int) ≠ 0 := hz
      simp [GenShiftRule.step, rule, embedCfg, embedTape, tapeUpdate, this]
  · simp [GenShiftRule.step, rule, embedCfg, embedTape]

theorem sim_step {c : Cfg} {cfg : GenShiftCfg (Option Cfg)} (h : Rel M c cfg) :
    Rel M (M.step c) (GenShiftRule.step (rule M) cfg) := by
  cases h
  simpa [Rel] using step_embedCfg (M := M) c

theorem sim_halts {c : Cfg} {cfg : GenShiftCfg (Option Cfg)} (h : Rel M c cfg) :
    (M.halts c ↔ (sys M).halts cfg) := by
  cases h
  constructor
  · intro hc
    exact ⟨c, rfl, hc⟩
  · rintro ⟨c', hc', hc'Halts⟩
    have ht : embedTape c = embedTape c' := by
      simpa [embedCfg] using congrArg GenShiftCfg.tape hc'
    have h0 : (embedTape c) 0 = (embedTape c') 0 := by
      simpa using congrArg (fun t => t 0) ht
    have hsome : (some c : Option Cfg) = some c' := by
      simpa [embedTape] using h0
    cases hsome
    simpa using hc'Halts

end Embed

end Computation
end MirandaDynamics
end HeytingLean
