import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteBoundary

/-!
# MirandaDynamics.Billiards: Appendix-consistent redirecting walls `\\widetilde W` (WS7.3)

The repo’s original `tildeWall` definition kept the same `+2` vertical offset as `rwWall`.
In the Appendix (arXiv:2512.19156, around `tmp_paper/arxiv.tex:541`), however, the redirecting
walls `\\widetilde W` are translated **down by 2** compared to the separating walls `W`.

This file introduces a second, Appendix-consistent redirecting wall family, without modifying
the existing toy `tildeWall`.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set
open Plane

namespace PaperReadWrite

/-- Appendix-consistent redirecting wall: same x-domain shift as `tildeWall`, but with **no**
leading `+2` vertical offset (so the wall family sits near height `0`). -/
def tildeWallAppendix (k : ℤ) (ds : List Bool) (cur : Bool) : Set V :=
  { p |
      x p ∈ Set.Icc (rwBlockLeft k ds + shift cur) (rwBlockLeft k ds + shift cur + rwBlockLen k ds) ∧
      y p =
        (if cur then (-rwBlockCenter k ds + (x p - shift cur)) else (rwBlockCenter k ds - (x p - shift cur))) }

theorem mem_tildeWallAppendix_iff (k : ℤ) (ds : List Bool) (cur : Bool) (p : V) :
    p ∈ tildeWallAppendix k ds cur ↔
      x p ∈ Set.Icc (rwBlockLeft k ds + shift cur) (rwBlockLeft k ds + shift cur + rwBlockLen k ds) ∧
      y p =
        (if cur then (-rwBlockCenter k ds + (x p - shift cur)) else (rwBlockCenter k ds - (x p - shift cur))) :=
  Iff.rfl

/-- Canonical union of Appendix redirecting walls `tildeWallAppendix k (pref++[cur]) cur`. -/
def tildeWallAppendixUnionCanonical : Set V :=
  { p |
      ∃ k : ℤ, ∃ pref : List Bool, ∃ cur : Bool,
        PaperReadWriteBoundary.rwDigits k pref cur ∧ p ∈ tildeWallAppendix k (pref ++ [cur]) cur }

/-- `tildeWallAppendix` is a translation of `rwWall` by `(shift cur, -2)`. -/
theorem tildeWallAppendix_eq_image_translate_rwWall (k : ℤ) (ds : List Bool) (cur : Bool) :
    tildeWallAppendix k ds cur =
      (fun p : V => p + (shift cur) • eX + (-2 : ℝ) • eY) '' (rwWall k ds cur) := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨hx, hy⟩
    -- translate back to a point on `rwWall`.
    let q : V := p + (-shift cur) • eX + (2 : ℝ) • eY
    have hxq : x q ∈ rwBlockInterval k ds := by
      rcases hx with ⟨hxL, hxU⟩
      -- `x q = x p - shift cur`.
      have hxq' : x q = x p - shift cur := by
        simp [q, Plane.x, Plane.eX, Plane.eY, add_assoc, add_left_comm, add_comm]
      constructor <;> linarith [hxq']
    have hyq : y q = (2 : ℝ) + (if cur then (-rwBlockCenter k ds + x q) else (rwBlockCenter k ds - x q)) := by
      have hyq' : y q = y p + 2 := by
        simp [q, Plane.y, Plane.eX, Plane.eY, add_assoc, add_left_comm, add_comm]
      have hxq' : x q = x p - shift cur := by
        simp [q, Plane.x, Plane.eX, Plane.eY, add_assoc, add_left_comm, add_comm]
      cases cur <;> simp [tildeWallAppendix, hy, hyq', hxq'] <;> ring_nf
    have hq : q ∈ rwWall k ds cur := by
      refine ⟨hxq, ?_⟩
      simpa [rwWall, hyq]
    refine ⟨q, hq, ?_⟩
    -- show translating `q` gives back `p`
    have : p = q + (shift cur) • eX + (-2 : ℝ) • eY := by
      simp [q, add_assoc, add_left_comm, add_comm]
    simpa [this]
  · rintro ⟨q, hq, rfl⟩
    rcases hq with ⟨hxq, hyq⟩
    refine ⟨?_, ?_⟩
    · -- x-domain: translate `[left,right]` by `shift cur`.
      rcases hxq with ⟨hxL, hxU⟩
      have hx : x (q + shift cur • eX + (-2 : ℝ) • eY) = x q + shift cur := by
        simp [Plane.x, Plane.eX, Plane.eY, add_assoc, add_left_comm, add_comm]
      constructor <;> linarith [hx]
    · -- y-equation: translate down by 2.
      have hy : y (q + shift cur • eX + (-2 : ℝ) • eY) = y q - 2 := by
        simp [Plane.y, Plane.eX, Plane.eY, add_assoc, add_left_comm, add_comm]
      have hx : x (q + shift cur • eX + (-2 : ℝ) • eY) - shift cur = x q := by
        simp [Plane.x, Plane.eX, Plane.eY, add_assoc, add_left_comm, add_comm]
      cases cur <;> simp [tildeWallAppendix, hy, hx, rwWall] at hyq ⊢ <;> linarith

end PaperReadWrite

end Billiards
end MirandaDynamics
end HeytingLean
