import Mathlib.Order.Nucleus
import Mathlib.Data.Set.Lattice

/-!
# Flow Lens scaffolding (standalone minimal version)

Minimal definitions for Miranda dynamics: flow trajectories, loop detection,
and flow-based nucleus operators.

This is a standalone extract for the Miranda Dynamics PaperPack.
-/

namespace HeytingLean
namespace Bridges

abbrev FlowPoint := Array Float
abbrev FlowTraj  := Array FlowPoint

namespace Flow

/-- Euclidean distance between two flow points. -/
def l2Dist (a b : FlowPoint) : Float := Id.run do
  let n := min a.size b.size
  let mut s := 0.0
  for i in [0:n] do
    let d := a[i]! - b[i]!
    s := s + d * d
  return Float.sqrt s

/-- Norm of a flow point. -/
def pointNorm (p : FlowPoint) : Float := Id.run do
  let zero : FlowPoint := Array.replicate p.size 0.0
  return l2Dist p zero

/-- Dot product of two points. -/
def dot (a b : FlowPoint) : Float := Id.run do
  let n := min a.size b.size
  let mut s := 0.0
  for i in [0:n] do s := s + a[i]! * b[i]!
  return s

/-- Cosine similarity; returns 1.0 if a or b is zero. -/
def cosSim (a b : FlowPoint) : Float :=
  let na := pointNorm a
  let nb := pointNorm b
  if na == 0.0 || nb == 0.0 then 1.0 else (dot a b) / (na * nb)

/-- Check if a trajectory forms a simple loop. -/
def isLoop (posTol dirCosTol : Float) (t : FlowTraj) : Bool := Id.run do
  let n := t.size
  if n < 3 then return false
  let p0 := t[0]!
  let pN := t[n-1]!
  let close := (l2Dist p0 pN) ≤ posTol
  let v0 := Id.run do
    let a := t[0]!
    let b := t[1]!
    let m := min a.size b.size
    let mut d : FlowPoint := #[]
    for j in [0:m] do d := d.push (b[j]! - a[j]!)
    d
  let vN := Id.run do
    let a := t[n-2]!
    let b := t[n-1]!
    let m := min a.size b.size
    let mut d : FlowPoint := #[]
    for j in [0:m] do d := d.push (b[j]! - a[j]!)
    d
  let cos := cosSim v0 vN
  return close && (cos ≥ dirCosTol)

def loopSet (posTol dirCosTol : Float) : Set FlowTraj :=
  { t | isLoop posTol dirCosTol t = true }

/-- Identity nucleus on `Set FlowTraj`. -/
def flowNucleusId : Nucleus (Set FlowTraj) where
  toInfHom :=
  { toFun := id
    map_inf' := by intro _ _; rfl }
  idempotent' := by intro _; rfl
  le_apply' := by intro _; rfl

/-- Union-with-U nucleus on `Set FlowTraj`. -/
def flowNucleusUnion (U : Set FlowTraj) : Nucleus (Set FlowTraj) where
  toInfHom :=
  { toFun := fun S => S ∪ U
    map_inf' := by
      intro S T
      ext x; constructor <;> intro hx
      · rcases hx with hx | hx
        · exact And.intro (Or.inl hx.1) (Or.inl hx.2)
        · exact And.intro (Or.inr hx) (Or.inr hx)
      · rcases hx with ⟨h1, h2⟩
        cases h1 with
        | inl hS =>
          cases h2 with
          | inl hT => exact Or.inl ⟨hS, hT⟩
          | inr hU => exact Or.inr hU
        | inr hU => exact Or.inr hU }
  idempotent' := by
    intro S
    intro x hx; cases hx with
    | inl hxSU => cases hxSU with
      | inl hS => exact Or.inl hS
      | inr hU => exact Or.inr hU
    | inr hU => exact Or.inr hU
  le_apply' := by
    intro S
    intro x hx; exact Or.inl hx

def flowNucleusOsc (posTol dirCosTol : Float) : Nucleus (Set FlowTraj) :=
  flowNucleusUnion (loopSet posTol dirCosTol)

end Flow

end Bridges
end HeytingLean
