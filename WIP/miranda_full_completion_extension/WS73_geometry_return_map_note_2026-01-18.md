# WS7.3/Geometry → WS7.4/Paper Map Link (Research + Mapping)

Date: 2026-01-18

Goal: start the long-horizon proof that a billiard **return map** (Poincaré map on a suitable
cross-section / invariant set) coincides with the already-mechanized WS7.4 symbolic target
(`paperFctrl?`, piecewise affine on explicit Cantor/control blocks).

## Evidence (paper)

Source: Miranda–Ramos, “Classical billiards can compute” (arXiv:2512.19156, Dec 2025).

Accessible HTML mirror used during this pass:
- https://ar5iv.labs.arxiv.org/html/2512.19156

Key items visible in §3.1 (notation: `τ_k`, Cantor read/write, head index `k`):
- Head embedding `τ_k(x)` is affine in `x` with scale `1/4^k` and explicit offset.
- The update that overwrites the `k`-th Cantor digit and shifts head corresponds to an affine
  update `x ↦ x ± (1/4^{|k|})` on the Cantor coordinate plus an affine head-coordinate update.

Lean mapping:
- `CantorEncoding.lean` mechanizes `encodeTape`, `tau`/`headInterval`, and the shift law.
- `CantorDigits.lean` / `CantorCylinders.lean` / `CantorBlockExplicit.lean` mechanize digit-reading
  and explicit block domains.
- `PaperMapFiniteControl.lean` + `PaperMapFiniteControlBlocks.lean` package the full WS7.4 map
  (with finite control encoded in the head coordinate) as `paperFctrl?`, and prove it is explicitly
  affine on each branch block.

## What’s missing (geometry side)

The paper’s billiard construction requires:
- a billiard table and a cross-section (“phase space”) on which the billiard return map is
  well-defined (corner singularities excluded),
- a coding map from billiard collision states to `(x,z) ∈ ℝ²` landing in the WS7.4 invariant set,
- a proof that one return step equals the WS7.4 affine branch selected by `(k,q,cur)`.

This is not yet mechanized in the repo; current WS7.3 work only provides a proof-grade deterministic
`next?` map for the **unit square** (toy table), plus “good state” hypotheses ensuring `next?` is
defined.

## Immediate mechanizable subgoals (next)

1) Define a general “first return map” operator for partial deterministic maps (`α → Option α`):
   - `iterate?` helper,
   - `firstReturn?` to a section `S : α → Prop` (noncomputable via classical choice),
   - basic correctness lemmas (if defined then in section, minimality optionally deferred).

2) Prove iteration/return-map transfer lemmas:
   - if `Option.map encode (f s) = g (encode s)` (one-step semiconjugacy), then the same holds for
     `iterate? n f` vs `iterate? n g`,
   - specialize to `UnitSquareMap.next?` and `paperFctrl?` via the `UnitSquareMap.PaperLink` record
     (defined in `GeometryToPaperTarget.lean`).

These are “geometry-to-paper” scaffolding steps: they don’t build the paper’s billiard table, but
they put the *logical skeleton* of the return-map equality into a reusable, testable form.

## Status update (mechanized)

As of 2026-01-18, in addition to the iteration/return scaffolding, we now also have a fully
mechanized **one-step semiconjugacy** on the *symbolic* cross-section model:

- File: `lean/HeytingLean/MirandaDynamics/Billiards/GenShiftCtrlPaperLink.lean`
  - State space: `GenShiftCtrlCfg (Fin m) Bool` (controlled generalized shift configuration)
  - Partial map: `GenShiftCtrlMap.next? = some (GenShiftCtrlRule.step …)`
  - Encoding: `encodeCfgCtrl : GenShiftCtrlCfg → ℝ×ℝ`
  - Theorems:
    - `GenShiftCtrlMap.encodeCfgCtrl_mem_CtrlDomain`
    - `GenShiftCtrlMap.semiconj`
    - `GenShiftCtrlMap.semiconj_iter`
    - `GenShiftCtrlMap.ReturnRel_encode`

This is the exact algebraic/semantic “cross-section → paper map” statement that the real
geometric billiard construction must eventually realize (by constructing a billiard cross-section
state and a map to `GenShiftCtrlCfg`, or directly by constructing `UnitSquareMap.PaperLink` in
`GeometryToPaperTarget.lean`).

## Still missing (the real geometry)

What is *not* yet mechanized is the paper’s geometric content that produces the semiconjugacy from
an actual billiard table:

- A concrete billiard table geometry (walls/corridors/parabolic arcs) and a cross-section within
  its collision space.
- A coding `encode : CollisionState → ℝ×ℝ` from that cross-section into the WS7.4 coordinates.
- A proof that the billiard “next return” equals `paperFctrl?` on “good” (nonsingular) states.

In particular, the remaining hard parts of WS7.3 are still open:
- proving **no spurious collisions** with *other* walls in the (infinite) union of read/write wall
  segments (the Appendix’s inequality estimates are not yet formalized);
- defining and analyzing the **parabolic shift walls** and proving the correct head-shift affine
  update from specular reflection;
- turning the staged collision semantics into a deterministic “next collision / next return” map
  for the full table.

## New blocker: straight-gadget kinematics mismatch (needs resolution)

The repo currently contains **two incompatible straight-wall stories**, and this must be resolved
before corridor-level “no spurious collisions” can be upgraded to a true **minimal-time** billiard
`next?`:

1) **Specular-reflection collision model (`PaperReadWriteCollision.lean`)**
   - Incoming velocity is vertical (`eY`).
   - Walls `rwWall … cur` have slope `±1`.
   - Specular reflection across the tangent line sends `eY ↦ ±eX` (horizontal), proved by
     `ReadOnlyCollision.reflect_rwWallNormal_eY`.
   - This model underlies `PaperReadWriteTableReadOnly.lean` and the “deterministic first hit on the
     union” theorem `entry_hitPoint_unique`.

2) **Appendix-style flight-avoidance model (`PaperReadWriteFlightAvoidance.lean`)**
   - Defines *extremal* post-bounce “flight lines” `flightLineLeft0` / `flightLineRight1` which are
     **diagonal** (`y - x = const` or `y + x = const`), and proves they cannot intersect unintended
     walls (up to endpoint exclusions), matching the Appendix inequality argument.
   - These lemmas (and their cross-`k` extensions) do not apply to a **horizontal** post-bounce
     segment.

The arXiv Appendix text (v2, `tmp_paper/arxiv.tex:541`) says the post-bounce ray “travels along a
line of slope `-1`” between `W` and `\\widetilde W`, but with the stated wall slopes `±1` and a
vertical incoming ray, specular reflection yields a **horizontal** outgoing ray. Either:
- the intended “incoming” direction is not purely vertical (only `vy>0`), or
- the Appendix’s slope description is in a rotated coordinate frame, or
- the write-up has a sign/slope typo in that sentence.

**Action item:** pick a single coherent kinematic model (direction conventions + cross-section) and
then:
- re-derive the appropriate extremal-trajectory inequalities for that model, and
- reprove avoidance against `rwWallUnionCanonical ∪ tildeWallUnionCanonical` for the *actual* flight
  segments used by the deterministic `next?`.

**Update (2026-01-19): Appendix flight-line model selected.**
- New Appendix-consistent straight-gadget collision-space convention introduced in
  `lean/HeytingLean/MirandaDynamics/Billiards/PaperReadWriteCollisionAppendixFlight.lean`:
  the cross-section point is the *upper endpoint* of `rwWall k ds cur` and the outgoing direction is
  the diagonal extremal ray (`flightRayLeft0` / `flightRayRight1`) used by the Appendix.
- Quantitative cross-`k` endpoint-separation bounds extended to the **negative** head-index branch via
  reflection symmetry (`headLeft_neg` / `headRight_neg`) in
  `lean/HeytingLean/MirandaDynamics/Billiards/PaperReadWriteFlightAvoidanceCrossK.lean`
  (`endpointSepCross_negSucc_of_lt` and corresponding ray-disjointness lemmas).
- Mixed-sign cross-`k` bounds (nonnegative `k` vs negative `k'`) and unified “dispatch” lemmas added in
  `lean/HeytingLean/MirandaDynamics/Billiards/PaperReadWriteFlightAvoidanceCrossK.lean`
  (`endpointSepCross_ofNat_negSucc`, `rwWall_false_disjoint_flightRayLeft0_of_lt`,
  `rwWall_true_disjoint_flightRayRight1_of_lt`), with canonical-index wrappers in
  `lean/HeytingLean/MirandaDynamics/Billiards/PaperReadWriteFlightAvoidanceCanonical.lean`.

External pointers used while setting up the “reflection formula” algebra and Euclidean-space
infrastructure:
- Mathlib docs (Euclidean basics): https://leanprover-community.github.io/mathlib_docs/geometry/euclidean/basic.html
- Mathlib `Submodule.reflection` (reflection formulas): https://leanprover-community.github.io/mathlib_docs/analysis/inner_product_space/projection/reflection.html

Online search note (2026-01-18):
- Query: “Lean 4 billiard map formalization specular reflection”
  - Found Mathlib reflection API and inner product/Euclidean geometry modules, but no existing
    billiard-return-map formalization suitable for reuse; continue with project-local
    deterministic-`next?` scaffolding built on `Submodule.reflection`.

## Geometry prerequisites now mechanized

To support the eventual straight-wall and collision-time arguments in the Appendix, the following
foundational pieces are now formalized:

- `lean/HeytingLean/MirandaDynamics/Billiards/CantorCylinderInterval.lean`
  - Defines `cantorLeft`, `cantorWidth`, `cantorCylinderInterval`
  - Proves `cantorCylinder_eq_interval` (each finite cylinder is exactly a closed interval).

- `lean/HeytingLean/MirandaDynamics/Billiards/PaperReadWriteWalls.lean`
  - Encodes the Appendix read-only wall families as `Set`s (domains + line equations)
    using `τ_k` images of explicit cylinder intervals.

- `lean/HeytingLean/MirandaDynamics/Billiards/LineCollision.lean`
  - Generic ray–line intersection algebra via `timeToLine?` and `Line n c`.

- `lean/HeytingLean/MirandaDynamics/Billiards/PaperReadWriteCollision.lean`
  - A first deterministic **next-collision** implementation for the Appendix read-only walls:
    - cross-section states: vertical incoming rays under a specified `rwWall k ds cur`,
    - computes the unique hit point via `timeToLine?`,
    - reflects the velocity specularly via `reflect`,
    - proves `Good → next? = some …` and a fixed-line collision uniqueness lemma.
  - Also includes a mechanizable **two-bounce toy variant** (`next2?`) using an auxiliary
    `tildeWall` family, returning to vertical velocity and shifting the `x` coordinate by `±2`.
    This is **not** yet claimed to match the paper’s global corridor geometry; it exists to make
    the straight-wall reflection algebra executable in Lean.

- `lean/HeytingLean/MirandaDynamics/Billiards/PaperReadWriteBoundary.lean`
  - Packages the straight-wall read/write gadget families as global unions:
    `rwWallUnion`, `tildeWallUnion`, `rwWallRewriteUnion`.
  - Also provides a “canonical indexing” boundary `paperReadWriteBoundaryCanonical` matching the
    Appendix’s intended discretization (prefix of length `indexNat k` + digit).

- `lean/HeytingLean/MirandaDynamics/Billiards/PaperReadWriteNoSpurious.lean`
  - Transfers Cantor-cylinder disjointness to disjointness of `rwBlockInterval` x-domains:
    `rwBlockInterval_eq_image_tau`, `rwBlockInterval_disjoint_of_length_eq`,
    and canonical uniqueness `rwBlockInterval_eq_of_mem_of_rwDigits`.
  - Also shows `rwBlockInterval k ds ⊆ headInterval k`, so different `k`-families are disjoint.
  - New quantitative separation spine (Appendix inequality prerequisites):
    - `rwBlockLeft_separated_of_length_eq`: same-length distinct blocks satisfy
      `|rwBlockLeft k ds - rwBlockLeft k ds'| ≥ 2 * rwBlockLen k ds`.

- `lean/HeytingLean/MirandaDynamics/Billiards/PaperReadWriteFlightAvoidance.lean`
  - Appendix-style *flight-line* avoidance lemma for the straight read-only wall family:
    the “extremal” down-left ray from the left endpoint of `rwWall … cur=false` cannot intersect any
    other same-level (`k`), same-cur wall segment except (at most) at an excluded endpoint.
  - Provides the ray-level disjointness wrapper
    `rwWall_false_disjoint_flightRayLeft0_of_ne` (excluding endpoint hits).
  - Symmetric `cur=true` variant:
    `flightLineRight1`, `flightRayRight1`, and corresponding disjointness lemmas.

- `lean/HeytingLean/MirandaDynamics/Billiards/PaperReadWriteFlightAvoidanceCrossK.lean`
  - Introduces `PaperReadWrite.endpointSepCross` (in `PaperReadWriteNoSpurious.lean`) to express the
    Appendix endpoint-separation inequality across **different** head indices `k ≠ k'`.
  - Proves cross-`k` “intersection forces endpoint” lemmas for both `cur=false` and `cur=true` using
    `endpointSepCross`, plus disjointness corollaries (intersection with strict interior is impossible).
  - Proves a quantitative `endpointSepCross` bound for **nonnegative** head indices (`k = ofNat n`,
    `k' = ofNat m`, `m < n`) using only coarse estimates (`cantorWidth ≤ 1/3`) and head-interval gap
    scaling; derives ray-level disjointness corollaries for this regime.
  - Status: still **partial** — negative-index symmetry and full union-level corridor avoidance remain open.

- `lean/HeytingLean/MirandaDynamics/Billiards/PaperReadWriteCorridorReadOnly.lean`
  - Corridor-local two-bounce wrapper for the canonical read-only gadget:
    `ReadOnlyCollisionCanonical.next2?`.
  - Collision-point membership in `tildeWallUnionCanonical` and a point-level uniqueness lemma:
    `tildeWallUnionCanonical_unique_of_hit`.

- `lean/HeytingLean/MirandaDynamics/Billiards/PaperReadWriteTableReadOnly.lean`
  - A staged `Geometry.Table` whose boundary is `rwWallUnionCanonical` (read-only straight walls).
  - Proves a first **global/union-level** deterministic next-collision uniqueness theorem for
    entry vertical rays (`entry_hitPoint_unique`).
  - Begins the WS7.3→WS7.4 symbol bridge by decoding the Cantor digit read from the block data
    (`entry_decode_digit`).

- `lean/HeytingLean/MirandaDynamics/Billiards/PaperReadWriteTableReadOnlyTwoBounce.lean`
  - Extends the staged table boundary to `rwWallUnionCanonical ∪ tildeWallUnionCanonical` and
    packages a two-step *reachability* witness `entryState ⟶ hitPoint ⟶ hitPoint₂`.
  - Still missing: segment-level avoidance showing no intermediate wall hits before `hitPoint₂`.

- `lean/HeytingLean/MirandaDynamics/Billiards/GeometryDeterministicNext.lean`
  - Adds a semantics-first **noncomputable** deterministic `next?` constructor from existence +
    uniqueness of a *first-hit time* (excludes corners/tangencies by hypothesis).

- `lean/HeytingLean/MirandaDynamics/Billiards/PaperReadWriteTableReadOnlyDeterministic.lean`
  - Instantiates `GeometryDeterministicNext` on the read-only entry cross-section:
    `entry_hitPoint_unique` implies `DeterministicNext.Good`, hence a definable `next?` on that
    cross-section (still staged, not the full paper table).

- `lean/HeytingLean/MirandaDynamics/Billiards/ParabolicShiftCorridor.lean`
  - Two-parabola common-focus corridor induces an affine horizontal map
    `x ↦ a + (f₂/f₁) * (x - a)` and specializes to the paper’s `headShift` branches.
  - Includes a deterministic cross-section `ParabolicShiftCorridor.CollisionState` with `next?`
    and theorems `nextCoord_eq_headShift` and `nextCoord_tau`.
    - `rwBlockLeft_sub_right_ge_len_of_left_gt`: an “endpoint gap” inequality under an ordering
      hypothesis, suitable for endpoint-based collision exclusion arguments.
    - `endpointSep` + `endpointSep_of_length_eq_of_left_gt`: packages the Appendix endpoint
      inequality in a reusable form.

- `lean/HeytingLean/MirandaDynamics/Billiards/ParabolicShiftCorridorTable.lean`
  - Packages the two-parabola affine-update computation into the staged billiard `Table.Step`
    semantics (`Geometry.lean`) for **single-parabola** tables:
    vertical-down flight → first parabola reflection → flight to `innerHit` on second parabola →
    second reflection yields a vertical-down outgoing direction.
  - Still staged (two tables; no global union boundary / minimal-time `next?` yet), but it is a
    concrete bridge from the parabola reflection lemmas to WS7.3 collision-step statements.

- `lean/HeytingLean/MirandaDynamics/Billiards/ParabolicShiftWalls.lean`
  - Formalizes the algebraic core of the parabola reflection property via `reflect_apply`:
    a vertical ray reflects toward the focus (`Parabola.reflect_neg_eY_eq_smul_focus_sub`) and
    conversely a ray aimed at the focus reflects to a vertical ray
    (`Parabola.reflect_focus_sub_eq_smul_neg_eY`).

- `lean/HeytingLean/MirandaDynamics/Billiards/CantorCylinderInterval.lean`
  - New quantitative Cantor-gap lemma:
    `cantorLeft_separated_of_length_eq` gives
    `|cantorLeft ds - cantorLeft ds'| ≥ 2 * cantorWidth ds` for same-length distinct digit lists.

- `lean/HeytingLean/MirandaDynamics/Billiards/CantorEncoding.lean`
  - Uniform interval bounds: `headInterval k ⊆ [0,1]` via `headInterval_subset_Icc`.

## Cross-section-level PaperLink (non-geometric)

For the semiconjugacy interface itself (ignoring the geometric realization), we now have a
“paper billiard” cross-section model:

- `lean/HeytingLean/MirandaDynamics/Billiards/PaperBilliardMap.lean`
  - State space: points of `CtrlDomain m` (already in WS7.4 coordinates).
  - `encode := id` and `next? := paperFctrl?` lifted to `CtrlDomain`.
  - Proves `PaperBilliardMap.semiconj` and `PaperBilliardMap.semiconj_iter` by definition.

This is *not* yet the real billiard table. It exists so that once a genuine geometric
`next?` is constructed, it can be plugged into the same `PaperLink`/return-map skeleton.
