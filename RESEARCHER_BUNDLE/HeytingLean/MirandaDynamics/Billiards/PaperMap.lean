import HeytingLean.MirandaDynamics.Billiards.CantorEncoding
import HeytingLean.MirandaDynamics.Billiards.CantorTapeUpdate

/-!
# MirandaDynamics.Billiards: a paper-level partial map on the Cantor/head invariant set (WS7.4)

This file extracts a minimal, fully mechanized *map-level* fragment from Miranda–Ramos
“Classical billiards can compute” (arXiv:2512.19156, Dec 2025):

* The **head-coordinate** update is piecewise-affine (paper Lemma 1), realized here via `headShift`.
* We package it as a partial function `paperF? : (ℝ × ℝ) → Option (ℝ × ℝ)` that is defined exactly
  when the head coordinate lies in one of the disjoint intervals `headInterval k`.

This is a staging point: it proves a conjugacy statement for the already-mechanized
`encodeWithHead` spine (shift-only skeleton). The read/write map acting on the tape coordinate is
left for a later WS7.4 milestone.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set

/-- A partial decoder extracting the unique head index `k` such that `z ∈ headInterval k`. -/
noncomputable def headIndex? (z : ℝ) : Option ℤ := by
  classical
  exact if h : ∃ k : ℤ, z ∈ headInterval k then some (Classical.choose h) else none

theorem headIndex?_eq_some_of_mem {z : ℝ} {k : ℤ} (hz : z ∈ headInterval k) :
    headIndex? z = some k := by
  classical
  have h : ∃ k' : ℤ, z ∈ headInterval k' := ⟨k, hz⟩
  have hz' : z ∈ headInterval (Classical.choose h) := Classical.choose_spec h
  have hk : Classical.choose h = k := by
    by_contra hne
    have hdis : Disjoint (headInterval (Classical.choose h)) (headInterval k) :=
      headInterval_disjoint (k := Classical.choose h) (k' := k) hne
    exact (Set.disjoint_left.1 hdis) hz' hz
  -- Unfold the `if` and rewrite by uniqueness of the interval index.
  simp [headIndex?, h, hk]

/-- The paper’s (piecewise-affine) head shift, packaged as a partial function. -/
noncomputable def headStep? (z : ℝ) : Option ℝ :=
  match headIndex? z with
  | none => none
  | some k => some (headShift k z)

theorem headStep?_eq_some_of_mem {z : ℝ} {k : ℤ} (hz : z ∈ headInterval k) :
    headStep? z = some (headShift k z) := by
  simp [headStep?, headIndex?_eq_some_of_mem (z := z) (k := k) hz]

theorem headStep?_encodeWithHead (t : Tape) (k : ℤ) :
    headStep? (encodeWithHead t k) = some (encodeWithHead t (k + 1)) := by
  have hz : encodeWithHead t k ∈ headInterval k :=
    tau_mem_headInterval (k := k) (x := encodeTape t) (encodeTape_mem_Icc t)
  have hk : headIndex? (encodeWithHead t k) = some k :=
    headIndex?_eq_some_of_mem (z := encodeWithHead t k) (k := k) hz
  -- Reduce to the already mechanized shift law for `encodeWithHead`.
  simp [headStep?, hk, headShift, encodeWithHead_shift]

/-- A minimal WS7.4 “paper map” on `ℝ²`: it updates only the head coordinate (shift-only skeleton). -/
noncomputable def paperF? : (ℝ × ℝ) → Option (ℝ × ℝ)
  | (x, z) =>
      match headIndex? z with
      | none => none
      | some k => some (x, headShift k z)

theorem paperF?_eq_some_of_head_mem {x z : ℝ} {k : ℤ} (hz : z ∈ headInterval k) :
    paperF? (x, z) = some (x, headShift k z) := by
  have hk : headIndex? z = some k := headIndex?_eq_some_of_mem (z := z) (k := k) hz
  simp [paperF?, hk]

theorem paperF?_encode_pair (t : Tape) (k : ℤ) :
    paperF? (encodeTape t, encodeWithHead t k) = some (encodeTape t, encodeWithHead t (k + 1)) := by
  have hz : encodeWithHead t k ∈ headInterval k :=
    tau_mem_headInterval (k := k) (x := encodeTape t) (encodeTape_mem_Icc t)
  -- Use the 1D conjugacy on the head coordinate.
  simp [paperF?, headIndex?_eq_some_of_mem (z := encodeWithHead t k) (k := k) hz, headShift,
    encodeWithHead_shift]

theorem paperF?_preserves_headIntervals {x z z' : ℝ} (h : paperF? (x, z) = some (x, z')) :
    (∃ k : ℤ, z ∈ headInterval k) → (∃ k : ℤ, z' ∈ headInterval k) := by
  classical
  rintro ⟨k, hz⟩
  have hk : headIndex? z = some k := headIndex?_eq_some_of_mem (z := z) (k := k) hz
  have hz' : z' = headShift k z := by
    -- `simp` reduces the `Option` equality to an equality of second components.
    have : headShift k z = z' := by
      simpa [paperF?, hk] using h
    simpa using this.symm
  refine ⟨k + 1, ?_⟩
  -- `headShift` transports `headInterval k` into `headInterval (k+1)`.
  simpa [hz'] using headShift_mem_headInterval_succ k hz

/-! ## A “write + shift” map fragment (piecewise affine once the digit branch is fixed) -/

noncomputable def writeDelta (k : ℤ) (b cur : Bool) : ℝ :=
  (2 / 3 : ℝ) *
    ((bif b then ((3 : ℝ)⁻¹) ^ (indexNat k) else 0) - (bif cur then ((3 : ℝ)⁻¹) ^ (indexNat k) else 0))

/-- A map fragment that overwrites the current head cell (given its digit `cur`) with `b`
and then shifts the head from `k` to `k+1`. -/
noncomputable def paperWriteF? (b cur : Bool) : (ℝ × ℝ) → Option (ℝ × ℝ)
  | (x, z) =>
      match headIndex? z with
      | none => none
      | some k =>
          let x' := x + writeDelta k b cur
          some (x', tau (k + 1) x')

theorem paperWriteF?_encode_pair (t : Tape) (k : ℤ) (b : Bool) :
    paperWriteF? b (t k) (encodeTape t, encodeWithHead t k) =
      some (encodeTape (Tape.write t k b), encodeWithHead (Tape.write t k b) (k + 1)) := by
  have hz : encodeWithHead t k ∈ headInterval k :=
    tau_mem_headInterval (k := k) (x := encodeTape t) (encodeTape_mem_Icc t)
  have hk : headIndex? (encodeWithHead t k) = some k :=
    headIndex?_eq_some_of_mem (z := encodeWithHead t k) (k := k) hz
  have hkτ : headIndex? (tau k (encodeTape t)) = some k := by
    simpa [encodeWithHead] using hk
  have hx :
      encodeTape (Tape.write t k b) =
        encodeTape t + writeDelta k b (t k) := by
    simpa [writeDelta] using (encodeTape_write_eq_add_pow (t := t) (k := k) (b := b))
  -- Compute the output and rewrite the updated tape coordinate using `hx`.
  simp [paperWriteF?, hkτ, encodeWithHead, hx, writeDelta]

end Billiards
end MirandaDynamics
end HeytingLean
