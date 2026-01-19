import HeytingLean.MirandaDynamics.TKFT.PartialFlowReaching

/-!
# miranda_partialflow_demo

Runtime smoke test for the `Dynamics.PartialFlow` packaging.

This demo uses the explicit total flow `x ↦ x + t` on `Nat` (viewed as a partial flow with `dom := True`)
to exercise:
- C backend compilation/linking for `PartialFlow`-dependent code,
- basic runtime behavior (no file IO; safe under hostile env/PATH checks).
-/

namespace HeytingLean
namespace MirandaDynamics

namespace PartialFlowDemo

open TKFT
open Dynamics

def addFlow : PartialFlow Nat Nat :=
  { dom := fun _t _x => True
    map := fun t x => x + t
    dom_zero := fun _x => True.intro
    map_zero := by intro x; simp
    dom_add := by intro _t₁ _t₂ _x _h₂ _h₁; exact True.intro
    map_add := by
      intro t₁ t₂ x _h₂ _h₁
      simp [Nat.add_left_comm, Nat.add_comm] }

def main (_argv : List String) : IO UInt32 := do
  IO.println "[miranda_partialflow_demo] PartialFlow (Nat action by addition)"
  let x : Nat := 10
  let t : Nat := 5
  let y := addFlow.map t x
  IO.println s!"[demo] x={x} t={t} map t x = {y}"
  IO.println s!"[demo] map 0 x = {addFlow.map 0 x}"

  -- Show a concrete reaching witness (not decidable in general; we just print the witness data).
  let In : Set Nat := {n | n = x}
  let Out : Set Nat := {n | n = y}
  let R := TKFT.PartialFlow.reachingRelOfPartialFlow (ϕ := addFlow) In Out
  have hx : x ∈ In := by simp [In]
  have hy : y ∈ Out := by simp [Out]
  have : R.rel ⟨x, hx⟩ ⟨y, hy⟩ := by
    refine ⟨t, True.intro, ?_⟩
    rfl
  IO.println s!"[demo] produced reach witness for x ↝ y via t={t}"
  -- ensure the proof is used (but still erases at runtime)
  let _ := this

  return 0

end PartialFlowDemo

end MirandaDynamics
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.MirandaDynamics.PartialFlowDemo.main args
