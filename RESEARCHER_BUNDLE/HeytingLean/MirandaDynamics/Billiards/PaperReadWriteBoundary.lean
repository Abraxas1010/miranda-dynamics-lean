import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteWalls

/-!
# MirandaDynamics.Billiards: the read–write gadget boundary as a global union (WS7.3)

The Appendix of Miranda–Ramos (arXiv:2512.19156) defines infinitely many straight wall segments
implementing the read–write gadget:

* separating walls `rwWall k ds cur` (read-only case, slope `±1`);
* redirecting walls `tildeWall k ds cur` (parallel, shifted by `±2`);
* perturbed-slope separating walls `rwWallRewrite k ds cur` (symbol-change case).

This file packages these families as global boundary sets (unions over indices). Proving that
“good” trajectories only collide with the intended walls (no spurious collisions across the union)
is the remaining geometric task built on top of these definitions.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set

/-- The union of all (read-only) separating walls `rwWall k ds cur`. -/
def rwWallUnion : Set V :=
  { p | ∃ k : ℤ, ∃ ds : List Bool, ∃ cur : Bool, p ∈ rwWall k ds cur }

/-- The union of all redirecting walls `tildeWall k ds cur`. -/
def tildeWallUnion : Set V :=
  { p | ∃ k : ℤ, ∃ ds : List Bool, ∃ cur : Bool, p ∈ tildeWall k ds cur }

/-- The union of all perturbed-slope separating walls `rwWallRewrite k ds cur`. -/
def rwWallRewriteUnion : Set V :=
  { p | ∃ k : ℤ, ∃ ds : List Bool, ∃ cur : Bool, p ∈ rwWallRewrite k ds cur }

/-- The full boundary contributed by the read–write gadget wall families. -/
def paperReadWriteBoundary : Set V :=
  rwWallUnion ∪ tildeWallUnion ∪ rwWallRewriteUnion

/-- The Appendix’s intended indexing for read–write walls: a prefix of length `indexNat k` plus the current digit. -/
def rwDigits (k : ℤ) (pref : List Bool) (cur : Bool) : Prop :=
  pref.length = indexNat k

/-- Canonical read-only wall union (matches the Appendix’s “fix the head digit index” discretization). -/
def rwWallUnionCanonical : Set V :=
  { p | ∃ k : ℤ, ∃ pref : List Bool, ∃ cur : Bool, rwDigits k pref cur ∧ p ∈ rwWall k (pref ++ [cur]) cur }

/-- Canonical redirecting wall union. -/
def tildeWallUnionCanonical : Set V :=
  { p | ∃ k : ℤ, ∃ pref : List Bool, ∃ cur : Bool, rwDigits k pref cur ∧ p ∈ tildeWall k (pref ++ [cur]) cur }

/-- Canonical perturbed-slope wall union (symbol-change case). -/
def rwWallRewriteUnionCanonical : Set V :=
  { p | ∃ k : ℤ, ∃ pref : List Bool, ∃ cur : Bool, rwDigits k pref cur ∧ p ∈ rwWallRewrite k (pref ++ [cur]) cur }

/-- Canonical boundary contributed by the read–write gadget wall families. -/
def paperReadWriteBoundaryCanonical : Set V :=
  rwWallUnionCanonical ∪ tildeWallUnionCanonical ∪ rwWallRewriteUnionCanonical

end Billiards
end MirandaDynamics
end HeytingLean
