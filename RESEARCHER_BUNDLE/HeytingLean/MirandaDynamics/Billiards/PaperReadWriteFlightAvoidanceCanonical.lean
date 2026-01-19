import HeytingLean.MirandaDynamics.Billiards.PaperReadWriteFlightAvoidanceCrossK

/-!
# MirandaDynamics.Billiards: canonical-index versions of cross-`k` avoidance (WS7.3)

`PaperReadWriteFlightAvoidanceCrossK` provides quantitative disjointness lemmas in terms of the raw
lists `ds : List Bool`.  The Appendix, however, uses the *canonical* indexing:
`ds = pref ++ [cur]` with `pref.length = indexNat k`.

This file instantiates the cross-`k` avoidance lemmas to that canonical shape, so downstream
deterministic-`next?` proofs can work directly with `rwWallUnionCanonical`.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set
open Plane

namespace PaperReadWrite

open PaperReadWriteNoSpurious

/-! ## Canonical disjointness (`cur=false`, left-going rays) -/

theorem rwWall_false_disjoint_flightRayLeft0_of_lt_canonical
    (k k' : ℤ) (hk : k' < k) (pref : List Bool) (pref' : List Bool)
    (hL : PaperReadWriteBoundary.rwDigits k pref false) (hL' : PaperReadWriteBoundary.rwDigits k' pref' false) :
    Disjoint
      (rwWall k' (pref' ++ [false]) false ∩
        {p : V | x p < rwBlockLeft k' (pref' ++ [false]) + rwBlockLen k' (pref' ++ [false])})
      (flightRayLeft0 k (pref ++ [false])) := by
  -- Canonical lists have positive length.
  have hds : 0 < (pref ++ [false]).length := by simp
  have hds' : 0 < (pref' ++ [false]).length := by simp
  simpa using
    rwWall_false_disjoint_flightRayLeft0_of_lt (k := k) (k' := k') hk (ds := pref ++ [false]) (ds' := pref' ++ [false])
      hds hds'

/-! ## Canonical disjointness (`cur=true`, right-going rays) -/

theorem rwWall_true_disjoint_flightRayRight1_of_lt_canonical
    (k k' : ℤ) (hk : k < k') (pref : List Bool) (pref' : List Bool)
    (hL : PaperReadWriteBoundary.rwDigits k pref true) (hL' : PaperReadWriteBoundary.rwDigits k' pref' true) :
    Disjoint
      (rwWall k' (pref' ++ [true]) true ∩ {p : V | rwBlockLeft k' (pref' ++ [true]) < x p})
      (flightRayRight1 k (pref ++ [true])) := by
  have hds : 0 < (pref ++ [true]).length := by simp
  have hds' : 0 < (pref' ++ [true]).length := by simp
  simpa using
    rwWall_true_disjoint_flightRayRight1_of_lt (k := k) (k' := k') hk (ds := pref ++ [true]) (ds' := pref' ++ [true])
      hds hds'

/-! ## Canonical wrappers for the easy cross-`k` rewrite-wall exclusions -/

theorem rwWallRewrite_disjoint_flightRayLeft0_of_k_lt_canonical
    (k k' : ℤ) (hk : k < k') (pref : List Bool) (pref' : List Bool) (cur' : Bool) :
    Disjoint (rwWallRewrite k' (pref' ++ [cur']) cur') (flightRayLeft0 k (pref ++ [false])) := by
  simpa using
    rwWallRewrite_disjoint_flightRayLeft0_of_k_lt (k := k) (k' := k') (ds := pref ++ [false])
      (ds' := pref' ++ [cur']) (cur' := cur') hk

theorem rwWallRewrite_disjoint_flightRayRight1_of_k_gt_canonical
    (k k' : ℤ) (hk : k' < k) (pref : List Bool) (pref' : List Bool) (cur' : Bool) :
    Disjoint (rwWallRewrite k' (pref' ++ [cur']) cur') (flightRayRight1 k (pref ++ [true])) := by
  simpa using
    rwWallRewrite_disjoint_flightRayRight1_of_k_gt (k := k) (k' := k') (ds := pref ++ [true])
      (ds' := pref' ++ [cur']) (cur' := cur') hk

end PaperReadWrite

end Billiards
end MirandaDynamics
end HeytingLean
