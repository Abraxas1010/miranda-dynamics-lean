import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteCollision
import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteFlightAvoidance

/-!
# MirandaDynamics.Billiards: corridor-local deterministic next-collision (read-only straight gadget)

This file is a concrete milestone toward the WS7.3 “real geometry” gap:

* define a corridor-local cross-section for the Appendix **read-only** straight-wall gadget
  (canonical indexing at fixed `k`);
* provide a deterministic two-bounce map (first hit `rwWall`, then `tildeWall`);
* prove that the two collision points are members of the **canonical boundary unions** and are
  unique at the *collision point level* (no spurious membership in another canonical wall at the
  same time).

What this still does **not** prove (long-horizon):
* trajectory/segment-level avoidance across the *full* infinite boundary union, i.e. ruling out
  intermediate collisions with other walls before reaching `tildeWall`;
* a global minimal-time `next?` over the complete paper billiard boundary.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set
open Plane

namespace PaperReadWrite

open ReadOnlyCollision
open ReadOnlyCollisionCanonical

/-! ## Canonical two-bounce map (wrapper around the non-canonical construction) -/

namespace ReadOnlyCollisionCanonical

/-- Forget the canonical length witness (just keep `ds = pref ++ [cur]`). -/
def toNoncanonical (s : State) : ReadOnlyCollision.State :=
  { k := s.k
    ds := s.ds
    cur := s.cur
    x0 := s.x0
    hx0 := s.hx0 }

@[simp] theorem toNoncanonical_k (s : State) : (toNoncanonical s).k = s.k := rfl
@[simp] theorem toNoncanonical_ds (s : State) : (toNoncanonical s).ds = s.ds := rfl
@[simp] theorem toNoncanonical_cur (s : State) : (toNoncanonical s).cur = s.cur := rfl
@[simp] theorem toNoncanonical_x0 (s : State) : (toNoncanonical s).x0 = s.x0 := rfl

theorem Good.toNoncanonical (s : State) (h : Good s) : ReadOnlyCollision.Good (toNoncanonical s) := by
  simpa [ReadOnlyCollision.Good, Good, ReadOnlyCollision.State.ds] using h

/-- Canonical two-bounce step: reuse `ReadOnlyCollision.next2?` through `toNoncanonical`. -/
noncomputable def next2? (s : State) : Option (V × V) :=
  ReadOnlyCollision.next2? (toNoncanonical s)

theorem next2?_eq_some_of_Good (s : State) (hgood : Good s) :
    ∃ q₂ : V, ∃ q₁ : V,
      next2? s = some (q₂, eY) ∧
      q₁ ∈ rwWall s.k s.ds s.cur ∧
      q₂ ∈ tildeWall s.k s.ds s.cur ∧
      x q₂ = s.x0 + shift s.cur := by
  have hgood' : ReadOnlyCollision.Good (toNoncanonical s) := Good.toNoncanonical s hgood
  simpa [next2?, toNoncanonical, ReadOnlyCollision.State.ds] using
    (ReadOnlyCollision.next2?_eq_some_of_Good (s := toNoncanonical s) hgood')

theorem next2?_encode_x (s : State) (hgood : Good s) :
    Option.map (fun out : V × V => x out.1) (next2? s) = some (s.x0 + shift s.cur) := by
  rcases next2?_eq_some_of_Good (s := s) hgood with ⟨q₂, _q₁, hnext2, _hq₁, _hq₂, hx⟩
  simp [next2?, hnext2, hx]

end ReadOnlyCollisionCanonical

/-! ## Canonical boundary membership and point-level uniqueness -/

namespace ReadOnlyCollisionCanonical

/-- The second collision point lies on the canonical redirecting wall union. -/
theorem next2?_hit_mem_tildeWallUnionCanonical (s : State) (hgood : Good s) :
    ∃ q₂ : V, q₂ ∈ tildeWallUnionCanonical ∧ next2? s = some (q₂, eY) := by
  rcases next2?_eq_some_of_Good (s := s) hgood with ⟨q₂, _q₁, hnext2, _hq₁, hq₂, _hx⟩
  refine ⟨q₂, ?_, hnext2⟩
  refine ⟨s.k, s.pref, s.cur, ?_, ?_⟩
  · simpa [PaperReadWriteBoundary.rwDigits] using s.hlen
  · simpa [tildeWallUnionCanonical, PaperReadWriteBoundary.rwDigits, ds, State.ds] using hq₂

/-- Point-level uniqueness for canonical `tildeWall` hits: if a point is on the intended `tildeWall`
and also on the canonical union, the index must match. -/
theorem tildeWallUnionCanonical_unique_of_hit (s : State) {q : V}
    (hq : q ∈ tildeWall s.k s.ds s.cur) (hq' : q ∈ tildeWallUnionCanonical) :
    ∃ pref' cur', pref' = s.pref ∧ cur' = s.cur := by
  rcases hq' with ⟨k', pref', cur', hk', hq'wall⟩
  -- Shifted interval membership reduces `tildeWall` to an unshifted block membership.
  let u : ℝ := x q - shift s.cur
  let u' : ℝ := x q - shift cur'
  have hu : u ∈ rwBlockInterval s.k s.ds := by
    simpa [u] using (mem_tildeWall_iff (k := s.k) (ds := s.ds) (cur := s.cur) (p := q)).1 hq |>.1
  have hu' : u' ∈ rwBlockInterval k' (pref' ++ [cur']) := by
    simpa [u'] using (mem_tildeWall_iff (k := k') (ds := pref' ++ [cur']) (cur := cur') (p := q)).1 hq'wall |>.1
  -- Both underlying block coordinates lie in `[0,1]`.
  have hu01 : u ∈ Set.Icc (0 : ℝ) 1 := by
    have hsub : rwBlockInterval s.k s.ds ⊆ headInterval s.k :=
      rwBlockInterval_subset_headInterval (k := s.k) (ds := s.ds)
    exact headInterval_subset_Icc s.k (hsub hu)
  have hu'01 : u' ∈ Set.Icc (0 : ℝ) 1 := by
    have hsub : rwBlockInterval k' (pref' ++ [cur']) ⊆ headInterval k' :=
      rwBlockInterval_subset_headInterval (k := k') (ds := pref' ++ [cur'])
    exact headInterval_subset_Icc k' (hsub hu')
  -- `cur` is determined by the shift: otherwise we'd force a gap of size `4` between two numbers in `[0,1]`.
  have hcur : cur' = s.cur := by
    cases s.cur <;> cases cur' <;> try rfl
    · -- `s.cur=false`, `cur'=true`: `u = u' + 4`, impossible in `[0,1]`.
      have : u = u' + 4 := by
        -- `u = x+2` and `u' = x-2`.
        simp [u, u', shift]
        ring
      have hu_le : u ≤ 1 := hu01.2
      have hu'_ge : 0 ≤ u' := hu'01.1
      nlinarith [hu_le, hu'_ge, this]
    · -- `s.cur=true`, `cur'=false`: `u' = u + 4`, impossible in `[0,1]`.
      have : u' = u + 4 := by
        simp [u, u', shift]
        ring
      have hu'_le : u' ≤ 1 := hu'01.2
      have hu_ge : 0 ≤ u := hu01.1
      nlinarith [hu'_le, hu_ge, this]
  subst hcur
  -- Now `u = u'`, so we can compare unshifted block memberships.
  have hu'' : u ∈ rwBlockInterval k' (pref' ++ [s.cur]) := by simpa [u', u] using hu'
  -- Identify the unique canonical block at this `k` from interval membership.
  have hkEq : s.k = k' := by
    by_contra hkne
    have hdis :
        Disjoint (rwBlockInterval s.k s.ds) (rwBlockInterval k' (pref' ++ [s.cur])) :=
      rwBlockInterval_disjoint_of_k_ne (hk := hkne) (ds := s.ds) (ds' := pref' ++ [s.cur])
    exact (Set.disjoint_left.1 hdis) hu hu''
  subst hkEq
  have hEq : s.ds = pref' ++ [s.cur] := by
    have hslen : s.pref.length = indexNat s.k := s.hlen
    have hslen' : pref'.length = indexNat s.k := by simpa [PaperReadWriteBoundary.rwDigits] using hk'
    exact
      rwBlockInterval_eq_of_mem_of_rwDigits (k := s.k) (pref := s.pref) (pref' := pref') (cur := s.cur)
        (cur' := s.cur) (x := u) hslen hslen' (by simpa [State.ds, ds] using hu) hu''
  -- Extract `pref'` from the list equality.
  have hpref : pref' = s.pref := by
    have ht := congrArg (fun l => l.take s.pref.length) hEq.symm
    simpa [State.ds, ds, List.take_append_of_le_length, s.hlen] using ht
  exact ⟨pref', s.cur, hpref.symm, rfl⟩

end ReadOnlyCollisionCanonical

/-! ## A simpler entry cross-section with block selection by existence/uniqueness -/

namespace ReadOnlyCorridor

open ReadOnlyCollisionCanonical

/-- Entry cross-section state for the read-only gadget at a fixed `k`, storing only the real
coordinate `x0` and the fact that it lies strictly inside *some* canonical block at this `k`. -/
structure Entry where
  k : ℤ
  x0 : ℝ
  good :
    ∃ bc : List Bool × Bool,
      bc.1.length = indexNat k ∧
        x0 ∈ Set.Ioo (rwBlockLeft k (bc.1 ++ [bc.2])) (rwBlockLeft k (bc.1 ++ [bc.2]) + rwBlockLen k (bc.1 ++ [bc.2]))

noncomputable def block (e : Entry) : List Bool × Bool := Classical.choose e.good

theorem block_spec (e : Entry) :
    (block e).1.length = indexNat e.k ∧
      e.x0 ∈ Set.Ioo (rwBlockLeft e.k ((block e).1 ++ [(block e).2]))
        (rwBlockLeft e.k ((block e).1 ++ [(block e).2]) + rwBlockLen e.k ((block e).1 ++ [(block e).2])) :=
  Classical.choose_spec e.good

abbrev pref (e : Entry) : List Bool := (block e).1
abbrev cur (e : Entry) : Bool := (block e).2

theorem pref_length (e : Entry) : (pref e).length = indexNat e.k :=
  (block_spec e).1

theorem x0_mem_block_Ioo (e : Entry) :
    e.x0 ∈ Set.Ioo (rwBlockLeft e.k (pref e ++ [cur e]))
      (rwBlockLeft e.k (pref e ++ [cur e]) + rwBlockLen e.k (pref e ++ [cur e])) :=
  (block_spec e).2

theorem x0_mem_block_Icc (e : Entry) :
    e.x0 ∈ rwBlockInterval e.k (pref e ++ [cur e]) := by
  exact ⟨le_of_lt (x0_mem_block_Ioo e).1, le_of_lt (x0_mem_block_Ioo e).2⟩

/-- Canonical collision state obtained by choosing the unique enclosing block. -/
noncomputable def state (e : Entry) : ReadOnlyCollisionCanonical.State :=
  { k := e.k
    pref := pref e
    cur := cur e
    hlen := pref_length e
    x0 := e.x0
    hx0 := x0_mem_block_Icc e }

theorem state_Good (e : Entry) : ReadOnlyCollisionCanonical.Good (state e) := by
  simpa [ReadOnlyCollisionCanonical.Good, state, ReadOnlyCollisionCanonical.ds, x0_mem_block_Ioo]

/-- Deterministic two-bounce output (read-only gadget), defined by selecting the unique canonical
block containing `x0`. -/
noncomputable def next2? (e : Entry) : Option (V × V) :=
  ReadOnlyCollisionCanonical.next2? (state e)

theorem next2?_eq_some (e : Entry) :
    ∃ q₂ : V, ∃ q₁ : V,
      next2? e = some (q₂, eY) ∧
      q₁ ∈ rwWall e.k ((pref e) ++ [cur e]) (cur e) ∧
      q₂ ∈ tildeWall e.k ((pref e) ++ [cur e]) (cur e) ∧
      x q₂ = e.x0 + shift (cur e) := by
  simpa [next2?, state] using ReadOnlyCollisionCanonical.next2?_eq_some_of_Good (s := state e) (state_Good e)

/-! ### Determinism of the selected block -/

theorem block_unique (e : Entry) {bc : List Bool × Bool}
    (hbc :
      bc.1.length = indexNat e.k ∧
        e.x0 ∈ rwBlockInterval e.k (bc.1 ++ [bc.2])) :
    bc = block e := by
  classical
  -- Compare the two canonical blocks by interval membership (disjoint cylinders).
  have hEq :
      (pref e ++ [cur e]) = bc.1 ++ [bc.2] := by
    exact rwBlockInterval_eq_of_mem_of_rwDigits (k := e.k) (pref := pref e) (pref' := bc.1) (cur := cur e)
      (cur' := bc.2) (x := e.x0) (pref_length e) hbc.1 (x0_mem_block_Icc e) hbc.2
  -- Convert list equality to pair equality.
  -- Extract `pref` by `take`, and `cur` by `getLast?`.
  have hpref : bc.1 = pref e := by
    have ht := congrArg (fun l => l.take (pref e).length) hEq.symm
    simpa [List.take_append_of_le_length, pref_length e] using ht
  have hcur : bc.2 = cur e := by
    have hn : (pref e ++ [cur e]).getLast? = some (cur e) := by simp
    have hn' : (bc.1 ++ [bc.2]).getLast? = some bc.2 := by simp
    have : some bc.2 = some (cur e) := by
      simpa [hEq] using (hn'.trans hn.symm)
    simpa using Option.some.inj this
  -- Conclude.
  cases bc with
  | mk pref' cur' =>
      simp [block, pref, cur, hpref, hcur]

end ReadOnlyCorridor

end PaperReadWrite

end Billiards
end MirandaDynamics
end HeytingLean
