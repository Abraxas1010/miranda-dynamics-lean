import HeytingLean.MirandaDynamics.Geometry.Forms.Euclidean

/-!
# MirandaDynamics.Geometry.Forms: `d` within a set (chart-local surrogate)

Mathlib's differential form API currently provides `extDeriv` on normed spaces and also a "within a set"
variant `extDerivWithin`. It does not (in this project's Mathlib pin) provide a bundled manifold-level
exterior derivative.

This file adds a small wrapper around `extDerivWithin`, which is useful for later chart-local reasoning
and for "open subset of `ℝⁿ`" surrogates.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Geometry
namespace Forms

open scoped Topology

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exterior derivative of an unbundled form *within a set* `s`. -/
noncomputable def dWithin {n : ℕ} (ω : Form (E := E) n) (s : Set E) : Form (E := E) (n + 1) :=
  fun x => extDerivWithin ω s x

theorem dWithin_def {n : ℕ} (ω : Form (E := E) n) (s : Set E) :
    dWithin (E := E) ω s = fun x => extDerivWithin ω s x :=
  rfl

theorem dWithin_univ {n : ℕ} (ω : Form (E := E) n) : dWithin (E := E) ω Set.univ = d (E := E) ω := by
  funext x
  simp [dWithin, d, extDerivWithin_univ]

/-- `dWithin (dWithin ω s) s = 0` on the interior-closure locus (re-export of Mathlib). -/
theorem dWithin_dWithin_eqOn {n : ℕ} (ω : Form (E := E) n) (s : Set E) (r : WithTop ℕ∞)
    (hω : ContDiffOn ℝ r ω s) (hr : minSmoothness ℝ 2 ≤ r) (hs : UniqueDiffOn ℝ s) :
    Set.EqOn (dWithin (E := E) (dWithin (E := E) ω s) s) 0 (s ∩ closure (interior s)) := by
  simpa [dWithin] using (extDerivWithin_extDerivWithin_eqOn (ω := ω) (s := s) (r := r) hω hr hs)

/-- Pointwise form of `dWithin (dWithin ω s) s = 0` (re-export of Mathlib). -/
theorem dWithin_dWithin_eq_zero {n : ℕ} (ω : Form (E := E) n) (s : Set E) (r : WithTop ℕ∞) (x : E)
    (hω : ContDiffWithinAt ℝ r ω s x) (hr : minSmoothness ℝ 2 ≤ r) (hs : UniqueDiffOn ℝ s)
    (hx : x ∈ closure (interior s)) (hxs : x ∈ s) :
    dWithin (E := E) (dWithin (E := E) ω s) s x = 0 := by
  simpa [dWithin] using
    (extDerivWithin_extDerivWithin_apply (ω := ω) (s := s) (x := x) (r := r) hω hr hs hx hxs)

end Forms
end Geometry
end MirandaDynamics
end HeytingLean
