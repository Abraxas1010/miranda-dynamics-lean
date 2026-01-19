import HeytingLean.MirandaDynamics.Billiards.CantorCylinderInterval
import HeytingLean.MirandaDynamics.Billiards.SpecularReflection

/-!
# MirandaDynamics.Billiards: paper read–write wall families (geometry data)

This file encodes (as Lean `Set`s) the explicit straight-wall families described in the Appendix of
Miranda–Ramos, “Classical billiards can compute” (arXiv:2512.19156), for the read–write gadget.

At this stage we only formalize the **wall geometry data** (domains + line equations). Proving that
the billiard dynamics realizes the desired return map requires a deterministic “next collision”
construction and nontrivial collision-avoidance proofs; those are the remaining WS7.3 tasks.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set

/-! ## Coordinates and basic vectors in `ℝ²` -/

namespace Plane

open scoped RealInnerProductSpace

abbrev x (p : V) : ℝ := p 0
abbrev y (p : V) : ℝ := p 1

def eX : V := fun i => if i = 0 then 1 else 0
def eY : V := fun i => if i = 1 then 1 else 0

@[simp] theorem eX_x : x eX = 1 := by simp [eX, x]
@[simp] theorem eX_y : y eX = 0 := by simp [eX, y]
@[simp] theorem eY_x : x eY = 0 := by simp [eY, x]
@[simp] theorem eY_y : y eY = 1 := by simp [eY, y]

end Plane

open Plane

/-! ## Cantor block endpoints after applying `τ_k` -/

/-- Left endpoint of the `τ_k`-image of a cylinder interval. -/
noncomputable def rwBlockLeft (k : ℤ) (ds : List Bool) : ℝ :=
  tau k (cantorLeft ds)

/-- Length of the `τ_k`-image of a cylinder interval (using the scale `headScale k`). -/
noncomputable def rwBlockLen (k : ℤ) (ds : List Bool) : ℝ :=
  headScale k * cantorWidth ds

theorem rwBlockLen_pos (k : ℤ) (ds : List Bool) : 0 < rwBlockLen k ds := by
  have hk : 0 < headScale k := headScale_pos k
  have hw : 0 < cantorWidth ds := by
    unfold cantorWidth
    have : 0 < (3 : ℝ) ^ ds.length := by positivity
    exact inv_pos.2 this
  exact mul_pos hk hw

/-- The `τ_k`-image interval for a cylinder list `ds`. -/
noncomputable def rwBlockInterval (k : ℤ) (ds : List Bool) : Set ℝ :=
  Set.Icc (rwBlockLeft k ds) (rwBlockLeft k ds + rwBlockLen k ds)

/-- Center of a `rwBlockInterval`. -/
noncomputable def rwBlockCenter (k : ℤ) (ds : List Bool) : ℝ :=
  rwBlockLeft k ds + (rwBlockLen k ds) / 2

/-! ## The read-only separating walls `W^k_{…s}` (Appendix: no symbol change) -/

/-- The straight wall segment of slope `-1` (for `cur = false`) or `+1` (for `cur = true`)
placed above a `τ_k`-block.

This matches the Appendix formulas (up to our existing `τ_k` definition and the cylinder encoding).
-/
def rwWall (k : ℤ) (ds : List Bool) (cur : Bool) : Set V :=
  { p |
      x p ∈ rwBlockInterval k ds ∧
      y p =
        (2 : ℝ) +
          (if cur then (-rwBlockCenter k ds + x p) else (rwBlockCenter k ds - x p)) }

/-- The outward normal used for the read-only wall line equation.

For `cur=false` (slope `-1` line), the normal is proportional to `(1,1)`.
For `cur=true` (slope `+1` line), the normal is proportional to `(1,-1)`. -/
def rwWallNormal (cur : Bool) : V :=
  if cur then (eX - eY) else (eX + eY)

/-- Horizontal shift used in the Appendix’s read-only gadget: `-2` for `cur=false`, `+2` for `cur=true`. -/
noncomputable def shift (cur : Bool) : ℝ :=
  if cur then 2 else -2

/-- A second “redirecting” wall segment parallel to `rwWall`, used to return trajectories to vertical. -/
def tildeWall (k : ℤ) (ds : List Bool) (cur : Bool) : Set V :=
  { p |
      x p ∈ Set.Icc (rwBlockLeft k ds + shift cur) (rwBlockLeft k ds + shift cur + rwBlockLen k ds) ∧
      y p =
        (2 : ℝ) +
          (if cur then (-rwBlockCenter k ds + (x p - shift cur)) else (rwBlockCenter k ds - (x p - shift cur))) }

/-- Slope parameter used in the Appendix’s “symbol change” case (slightly perturbed from `1`). -/
noncomputable def rewriteSlope (k : ℤ) (ds : List Bool) : ℝ :=
  (1 : ℝ) / (1 + rwBlockLen k ds)

/-- The “rewrite” separating wall: same center and domain as `rwWall`, but with perturbed slope. -/
def rwWallRewrite (k : ℤ) (ds : List Bool) (cur : Bool) : Set V :=
  { p |
      x p ∈ rwBlockInterval k ds ∧
      y p =
        (2 : ℝ) +
          (if cur then (rewriteSlope k ds) * (-rwBlockCenter k ds + x p)
           else (rewriteSlope k ds) * (rwBlockCenter k ds - x p)) }

end Billiards
end MirandaDynamics
end HeytingLean
