import HeytingLean.MirandaDynamics.Billiards.CantorEncoding
import HeytingLean.MirandaDynamics.Billiards.CantorNucleus
import HeytingLean.MirandaDynamics.Billiards.CantorTapeUpdate
import HeytingLean.MirandaDynamics.Billiards.SpecularReflection
import HeytingLean.MirandaDynamics.Billiards.Geometry
import HeytingLean.MirandaDynamics.Billiards.UnitSquare
import HeytingLean.MirandaDynamics.Billiards.UnitSquareMap
import HeytingLean.MirandaDynamics.Billiards.PaperMap
import HeytingLean.MirandaDynamics.Billiards.PaperMapFull
import HeytingLean.MirandaDynamics.Billiards.PaperMapPiecewise
import HeytingLean.MirandaDynamics.Billiards.PaperMapGenShift
import HeytingLean.MirandaDynamics.Billiards.CantorBlocks
import HeytingLean.MirandaDynamics.Billiards.CantorBlockExplicit
import HeytingLean.MirandaDynamics.Billiards.PaperMapFiniteControl
import HeytingLean.MirandaDynamics.Billiards.PaperMapFiniteControlBlocks
import HeytingLean.MirandaDynamics.Topology.BettiComplexity

namespace HeytingLean
namespace Tests
namespace MirandaDynamics

open HeytingLean.MirandaDynamics

namespace Billiards

open HeytingLean.MirandaDynamics.Billiards

open scoped RealInnerProductSpace

example (n v : HeytingLean.MirandaDynamics.Billiards.V) :
    HeytingLean.MirandaDynamics.Billiards.reflect n (HeytingLean.MirandaDynamics.Billiards.reflect n v) = v :=
  HeytingLean.MirandaDynamics.Billiards.reflect_reflect n v

example (n : HeytingLean.MirandaDynamics.Billiards.V) :
    HeytingLean.MirandaDynamics.Billiards.reflect n n = -n :=
  HeytingLean.MirandaDynamics.Billiards.reflect_normal_eq_neg n

example (z : ℤ) : tapeIndex (indexNat z) = z :=
  tapeIndex_indexNat z

example : (1 / 9 : ℝ) ∈ headInterval (-1 : ℤ) ↔ (1 - (1 / 9 : ℝ)) ∈ headInterval (1 : ℤ) := by
  simpa using (headInterval_reflect (-1 : ℤ) (x := (1 / 9 : ℝ)))

example : Disjoint (headInterval (-1 : ℤ)) (headInterval (0 : ℤ)) := by
  have h : (-1 : ℤ) ≠ 0 := by norm_num
  exact headInterval_disjoint (-1 : ℤ) 0 h

example (t : Tape) (k : ℤ) :
    encodeWithHead t (k + 1) =
      (if k < 0 then 3 * encodeWithHead t k else encodeWithHead t k / 3 + 2 / 3) := by
  simpa using encodeWithHead_shift t k

example (k : ℤ) : Function.Injective fun t : Tape => encodeWithHead t k :=
  encodeWithHead_injective_tape k

example : Function.Injective fun p : Tape × ℤ => encodeWithHead p.1 p.2 :=
  encodeWithHead_injective_pair

example (k : ℤ) {z : ℝ} (hz : z ∈ headInterval k) :
    headShift k z ∈ headInterval (k + 1) :=
  headShift_mem_headInterval_succ k hz

example (S : Set ℝ) : cantorNucleus S = S ↔ cantorCompl ⊆ S :=
  cantorNucleus_fixed_iff (S := S)

example : UnitSquare.boundary ⊆ UnitSquare.region :=
  UnitSquare.boundary_subset_region

example {s s' : HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.CollisionState}
    (h : HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.stepRel s s') :
    UnitSquare.table.Step s.toState s'.toState :=
  HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.stepRel_to_tableStep h

example (s : HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.CollisionState)
    (hs : HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.Good s) :
    ∃! s' : HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.CollisionState,
      HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.stepRel s s' :=
  HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.existsUnique_stepRel_of_good s hs

example (s s' : HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.CollisionState) :
    HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.Reaches s s' ↔
      ∃ n : Nat, HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.nextIter? n s = some s' :=
  HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.Reaches_iff_exists_nextIter? s s'

example (t : Tape) (k : ℤ) :
    HeytingLean.MirandaDynamics.Billiards.paperF? (encodeTape t, encodeWithHead t k) =
      some (encodeTape t, encodeWithHead t (k + 1)) :=
  HeytingLean.MirandaDynamics.Billiards.paperF?_encode_pair t k

example (t : Tape) (k : ℤ) (b : Bool) :
    encodeTape (HeytingLean.MirandaDynamics.Billiards.Tape.write t k b) =
      encodeTape t +
        (2 / 3 : ℝ) *
          (Cardinal.cantorFunctionAux ((3 : ℝ)⁻¹) (Function.update (digits t) (indexNat k) b) (indexNat k) -
            Cardinal.cantorFunctionAux ((3 : ℝ)⁻¹) (digits t) (indexNat k)) :=
  HeytingLean.MirandaDynamics.Billiards.encodeTape_write t k b

example (t : Tape) (k : ℤ) (b : Bool) :
    encodeTape (HeytingLean.MirandaDynamics.Billiards.Tape.write t k b) =
      encodeTape t +
        (2 / 3 : ℝ) *
          ((bif b then ((3 : ℝ)⁻¹) ^ (indexNat k) else 0) - (bif t k then ((3 : ℝ)⁻¹) ^ (indexNat k) else 0)) :=
  HeytingLean.MirandaDynamics.Billiards.encodeTape_write_eq_add_pow t k b

example (t : Tape) (k : ℤ) (b : Bool) :
    HeytingLean.MirandaDynamics.Billiards.paperWriteF? b (t k) (encodeTape t, encodeWithHead t k) =
      some (encodeTape (HeytingLean.MirandaDynamics.Billiards.Tape.write t k b),
        encodeWithHead (HeytingLean.MirandaDynamics.Billiards.Tape.write t k b) (k + 1)) :=
  HeytingLean.MirandaDynamics.Billiards.paperWriteF?_encode_pair t k b

example (δ : Bool → Bool) (t : Tape) (k : ℤ) :
    HeytingLean.MirandaDynamics.Billiards.paperFfull? δ (encodeTape t, encodeWithHead t k) =
      some (encodeTape (HeytingLean.MirandaDynamics.Billiards.Tape.write t k (δ (t k))),
        encodeWithHead (HeytingLean.MirandaDynamics.Billiards.Tape.write t k (δ (t k))) (k + 1)) :=
  HeytingLean.MirandaDynamics.Billiards.paperFfull?_encode_pair δ t k

example (δ : Bool → Bool) (t : Tape) (k : ℤ) :
    HeytingLean.MirandaDynamics.Billiards.paperFpiece? δ (encodeTape t, encodeWithHead t k) =
      some (encodeTape (HeytingLean.MirandaDynamics.Billiards.Tape.write t k (δ (t k))),
        encodeWithHead (HeytingLean.MirandaDynamics.Billiards.Tape.write t k (δ (t k))) (k + 1)) :=
  HeytingLean.MirandaDynamics.Billiards.paperFpiece?_encode_pair δ t k

example (next : Bool → Bool × ℤ) (t : Tape) (k : ℤ) :
    HeytingLean.MirandaDynamics.Billiards.paperFgen? next
        (HeytingLean.MirandaDynamics.Billiards.encodeCfg (HeytingLean.MirandaDynamics.Billiards.toGenShiftCfg t k)) =
      some
        (HeytingLean.MirandaDynamics.Billiards.encodeCfg
          (HeytingLean.MirandaDynamics.Computation.GenShiftRule.step (α := Bool) ⟨next⟩
            (HeytingLean.MirandaDynamics.Billiards.toGenShiftCfg t k))) :=
  HeytingLean.MirandaDynamics.Billiards.paperFgen?_encodeCfg next t k

example (next : Bool → Bool × ℤ) (t : Tape) (k : ℤ) :
    let p :=
      HeytingLean.MirandaDynamics.Billiards.encodeCfg (HeytingLean.MirandaDynamics.Billiards.toGenShiftCfg t k)
    HeytingLean.MirandaDynamics.Billiards.paperFgen? next p =
      some (HeytingLean.MirandaDynamics.Billiards.paperFgenAffine next k (t k) p) := by
  classical
  intro p
  have hz : p.2 ∈ HeytingLean.MirandaDynamics.Billiards.headInterval k := by
    -- `encodeWithHead` lands in the correct head interval.
    simpa [HeytingLean.MirandaDynamics.Billiards.encodeCfg,
      HeytingLean.MirandaDynamics.Billiards.toGenShiftCfg,
      HeytingLean.MirandaDynamics.Billiards.encodeWithHead] using
      (HeytingLean.MirandaDynamics.Billiards.tau_mem_headInterval (k := k) (x := encodeTape t)
        (HeytingLean.MirandaDynamics.Billiards.encodeTape_mem_Icc t))
  have hcur :
      HeytingLean.MirandaDynamics.Billiards.cantorDigitAt? (HeytingLean.MirandaDynamics.Billiards.indexNat k) p.1 =
        some (t k) := by
    simpa [HeytingLean.MirandaDynamics.Billiards.encodeCfg, HeytingLean.MirandaDynamics.Billiards.toGenShiftCfg] using
      (HeytingLean.MirandaDynamics.Billiards.cantorDigitAt?_encodeTape_indexNat (t := t) (k := k))
  have hp : p ∈ HeytingLean.MirandaDynamics.Billiards.CantorBlock k (t k) := by
    exact ⟨hz, hcur⟩
  simpa using
    (HeytingLean.MirandaDynamics.Billiards.paperFgen?_eq_some_paperFgenAffine_of_mem (next := next) (k := k)
      (cur := t k) (p := p) hp)

example (m : ℕ) (hm : 0 < m) (next : Fin m → Bool → Fin m × Bool × ℤ) (t : Tape) (k : ℤ) (q : Fin m) :
    HeytingLean.MirandaDynamics.Billiards.paperFctrl? next
        (HeytingLean.MirandaDynamics.Billiards.encodeCfgCtrl (HeytingLean.MirandaDynamics.Billiards.toGenShiftCtrlCfg t k q)) =
      some
        (HeytingLean.MirandaDynamics.Billiards.encodeCfgCtrl
          (HeytingLean.MirandaDynamics.Computation.GenShiftCtrlRule.step (Q := Fin m) (α := Bool) ⟨next⟩
            (HeytingLean.MirandaDynamics.Billiards.toGenShiftCtrlCfg t k q))) :=
  HeytingLean.MirandaDynamics.Billiards.paperFctrl?_encodeCfgCtrl (m := m) hm next t k q

example (m : ℕ) (hm : 0 < m) (next : Fin m → Bool → Fin m × Bool × ℤ) :
    let x : ℝ := 0
    let z : ℝ := HeytingLean.MirandaDynamics.Billiards.tauState m (0 : ℤ) (⟨0, hm⟩ : Fin m) x
    let p : ℝ × ℝ := (x, z)
    HeytingLean.MirandaDynamics.Billiards.paperFctrl? next p =
      some (HeytingLean.MirandaDynamics.Billiards.paperFctrlAffine next (0 : ℤ) (⟨0, hm⟩ : Fin m) false p) := by
  classical
  intro x z p
  -- Put `p` in the explicit control block `(k=0, q=0, cur=false)` by choosing the `0`-digit cylinder witness.
  have hz : z ∈ HeytingLean.MirandaDynamics.Billiards.headStateInterval m (0 : ℤ) (⟨0, hm⟩ : Fin m) := by
    -- `tauState` lands in the correct state interval on `[0,1]`.
    have hxI : x ∈ Set.Icc (0 : ℝ) 1 := by simp [x]
    simpa [z] using
      (HeytingLean.MirandaDynamics.Billiards.tauState_mem_headStateInterval (m := m) hm (k := (0 : ℤ))
        (q := (⟨0, hm⟩ : Fin m)) (x := x) hxI)
  have hx : x ∈ HeytingLean.MirandaDynamics.Billiards.cantorDigitBlock 0 false := by
    refine ⟨[], by simp, ?_⟩
    -- `cantorCylinder [false]` holds for `x=0`.
    refine ⟨?_, ?_⟩
    ·
      change (x : ℝ) ∈ Set.Icc (0 : ℝ) HeytingLean.MirandaDynamics.Billiards.oneThird
      refine ⟨by simp [x], ?_⟩
      have h3 : (0 : ℝ) ≤ (3 : ℝ) := by norm_num
      dsimp [HeytingLean.MirandaDynamics.Billiards.oneThird]
      exact inv_nonneg.mpr h3
    · simp [HeytingLean.MirandaDynamics.Billiards.cantorCylinder,
        HeytingLean.MirandaDynamics.Billiards.cantorTailAffine, x]
  have hp : p ∈ HeytingLean.MirandaDynamics.Billiards.CtrlCantorBlockExplicit m (0 : ℤ) (⟨0, hm⟩ : Fin m) false := by
    exact ⟨hz, by simpa [p] using hx⟩
  simpa using
    (HeytingLean.MirandaDynamics.Billiards.paperFctrl?_eq_some_paperFctrlAffine_of_mem_explicit (m := m) hm
      (next := next) (k := (0 : ℤ)) (q := (⟨0, hm⟩ : Fin m)) (cur := false) (p := p) hp)

example (b : Bool) {x : ℝ} (hx : x ∈ HeytingLean.MirandaDynamics.Billiards.cantorHeadInterval b) :
    HeytingLean.MirandaDynamics.Billiards.cantorHeadDigit? x = some b :=
  HeytingLean.MirandaDynamics.Billiards.cantorHeadDigit?_eq_some_of_mem_headInterval hx

example (next : Bool → Bool × ℤ) :
    let x : ℝ := 0
    let z : ℝ := HeytingLean.MirandaDynamics.Billiards.tau (0 : ℤ) x
    let p : ℝ × ℝ := (x, z)
    HeytingLean.MirandaDynamics.Billiards.paperFgen? next p =
      some (HeytingLean.MirandaDynamics.Billiards.paperFgenAffine next (0 : ℤ) false p) := by
  classical
  intro x z p
  have hz : z ∈ HeytingLean.MirandaDynamics.Billiards.headInterval (0 : ℤ) := by
    -- `τ_0` maps `[0,1]` into `headInterval 0`.
    simpa [z] using
      (HeytingLean.MirandaDynamics.Billiards.tau_mem_headInterval (k := (0 : ℤ)) (x := x) (by
        simp [x]))
  have hxBlock : x ∈ HeytingLean.MirandaDynamics.Billiards.cantorDigitBlock 0 false := by
    refine ⟨[], by simp, ?_⟩
    -- `cantorCylinder [false]` holds for `x=0`.
    refine ⟨?_, ?_⟩
    ·
      -- `x=0` lies in the left third `[0,1/3]`.
      change x ∈ Set.Icc (0 : ℝ) HeytingLean.MirandaDynamics.Billiards.oneThird
      refine ⟨by simp [x], ?_⟩
      have h3 : (0 : ℝ) ≤ (3 : ℝ) := by norm_num
      -- Reduce `oneThird` and discharge with `inv_nonneg`.
      dsimp [HeytingLean.MirandaDynamics.Billiards.oneThird]
      exact inv_nonneg.mpr h3
    ·
      -- Tail is `0` and the base cylinder is `[0,1]`.
      simp [HeytingLean.MirandaDynamics.Billiards.cantorTailAffine,
        HeytingLean.MirandaDynamics.Billiards.cantorCylinder, x]
  have hp : p ∈ HeytingLean.MirandaDynamics.Billiards.CantorBlockExplicit (0 : ℤ) false := by
    exact ⟨hz, by simpa [p] using hxBlock⟩
  simpa using
    (HeytingLean.MirandaDynamics.Billiards.paperFgen?_eq_some_paperFgenAffine_of_mem_explicit (next := next)
      (k := (0 : ℤ)) (cur := false) (p := p) hp)

noncomputable def trivialTable (n : V) : Table :=
  { inside := Set.univ
    boundary := Set.univ
    normal := fun _ => n }

example (n v : V) : ‖reflect n v‖ = ‖v‖ := by
  let T := trivialTable n
  let s : State := ⟨0, v⟩
  let s' : State := ⟨v, reflect n v⟩
  have hStep : T.Step s s' := by
    refine ⟨v, by simp [T, trivialTable], ?_, rfl, rfl⟩
    refine ⟨(1 : ℝ), by norm_num, ?_, ?_⟩
    · simp [s]
    · intro x hx
      simp [T, trivialTable]
  have hnorm : ‖s'.vel‖ = ‖s.vel‖ :=
    HeytingLean.MirandaDynamics.Billiards.Table.Step.norm_vel_eq (T := T) (s := s) (s' := s') hStep
  -- Avoid `simp` here: we want to sanity-check the staged `Step.norm_vel_eq` pipeline.
  calc
    ‖reflect n v‖ = ‖s'.vel‖ := rfl
    _ = ‖s.vel‖ := hnorm
    _ = ‖v‖ := rfl

end Billiards

namespace Topology

open HeytingLean.MirandaDynamics.Topology

variable {V : Type} (G : SimpleGraph V)

example [Finite V] (h : G.IsTree) : cycleRank G = 0 :=
  cycleRank_eq_zero_of_isTree (G := G) h

end Topology

end MirandaDynamics
end Tests
end HeytingLean
