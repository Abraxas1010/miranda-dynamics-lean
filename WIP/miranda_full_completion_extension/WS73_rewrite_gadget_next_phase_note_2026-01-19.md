# WS7.3 — Rewrite gadget (symbol-change walls): collision model + avoidance reduction (next phase)

Date: 2026-01-19

## Goal of this sprint

Mechanize the “symbol change / rewrite” part of the Appendix read–write gadget *as far as possible*
without jumping to the full global billiard table:

1) add a deterministic collision-space cross-section for the *rewrite* separating walls
   `rwWallRewrite k ds cur` (the perturbed-slope walls);
2) record how the paper reduces “no spurious collisions” for rewrite trajectories to the
   already-proved read-only (`±1` slope) case, and what we would need in Lean to make that
   reduction fully formal.

## Paper facts we treat as authoritative (for guidance)

From Miranda–Ramos, “Classical billiards can compute”, Appendix (arXiv:2512.19156):

- Symbol change requires a small horizontal displacement and therefore the separating wall does
  not have slope exactly `±1`. The paper chooses an angle so that
  `tan α_k = 1 / (1 + 3^{-(3k+2)})` (in our formalization: `rewriteSlope = 1 / (1 + rwBlockLen)`).
- Avoidance is “strictly easier” in the rewrite case: rewrite trajectories descend “more steeply”
  than the read-only case, so it suffices to carry out the collision-avoidance check for the
  read-only (`±1` slope) configuration.

Source: Miranda–Ramos, “Classical billiards can compute”, arXiv:2512.19156 (Appendix excerpt around the
“symbol change” discussion; see `tmp_paper/arxiv.tex` around the “symbol change” section).

External links:
- `https://arxiv.org/abs/2512.19156`
- `https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Projection/Reflection.html`

## Existing Lean assets to reuse

- Wall geometry data:
  - `rwWallRewrite` and `rewriteSlope` in `lean/HeytingLean/MirandaDynamics/Billiards/PaperReadWriteWalls.lean`.
- Deterministic line-collision algebra:
  - `Line` / `timeToLine?` in `lean/HeytingLean/MirandaDynamics/Billiards/LineCollision.lean`.
- Specular reflection core (via mathlib’s `Submodule.reflection`):
  - `reflect` and its explicit formula in `lean/HeytingLean/MirandaDynamics/Billiards/SpecularReflection.lean`.
  - Underlying mathlib reflection API:
    `Mathlib.Analysis.InnerProductSpace.Projection.Reflection`.
- “No spurious collisions” scaffolding (interval disjointness, head-interval separation, etc.):
  - `PaperReadWriteNoSpurious.lean`
  - `PaperReadWriteFlightAvoidance*.lean` (straight-wall rays and cross-`k` exclusions)

## What’s mechanizable immediately (and implemented next)

### A. Deterministic collision with `rwWallRewrite` (vertical cross-section)

Implement a `RewriteCollision` cross-section analogous to `ReadOnlyCollision`, but using
`rwWallRewrite` as the target segment.

Key observations (make the proof easy):

- The `x`-domain of `rwWallRewrite` is still `rwBlockInterval k ds`, so all the interval-disjointness
  lemmas apply unchanged for uniqueness of which block is hit.
- The supporting line equation can be written with a normal of the form `(±m, 1)` where
  `m = rewriteSlope k ds`, and crucially `⟪n, eY⟫ = 1`, so `timeToLine?` is never `none`.
- The reflected velocity has negative `y`-component whenever `m < 1`, which follows from
  `rwBlockLen_pos` (so `1 + rwBlockLen > 1` and `m = 1/(1+rwBlockLen) < 1`).

This yields:

- a total `hitTime?` / `hitPoint?` for this cross-section,
- a deterministic `next?` step and boundary membership in `rwWallRewriteUnionCanonical`,
- point-level uniqueness on the canonical union (same pattern as the read-only file).

### B. Rewrite avoidance reduction (what remains)

The paper’s key reduction is qualitative: rewrite trajectories descend “more steeply” than the
read-only extremal rays, so the read-only avoidance check implies rewrite avoidance.

To formalize this in Lean we still need a *trajectory comparison lemma* of the form:

- define the actual post-collision “between-wall flight” family for rewrite (depends on the
  reflection of the incoming direction across `rwWallRewrite`), and
- prove it lies in a region that is “below” (in the relevant sense) the already-controlled
  read-only extremal flight set (`flightRayLeft0`/`flightRayRight1`), so any wall intersection
  would force an intersection in the read-only case.

This comparison is the hard part of “complete next phase” that remains long-horizon, but the
collision-space and algebraic ingredients can be completed now.

---

## Update (2026-01-19): implemented reduction skeleton + corridor-local deterministic between-wall step

New Lean modules:

- `lean/HeytingLean/MirandaDynamics/Billiards/PaperReadWriteWallsRewriteAppendix.lean`
  - defines `shiftRewrite` and the Appendix-consistent rewrite redirecting wall family
    `tildeWallRewriteAppendix` (a translate of `rwWallRewrite` by `(shiftRewrite, -2)`),
    plus `tildeWallRewriteAppendixUnionCanonical`.
- `lean/HeytingLean/MirandaDynamics/Billiards/PaperReadWriteFlightAvoidanceRewriteReduction.lean`
  - defines half-spaces `belowFlightLineLeft0` / `belowFlightLineRight1` and proves the key
    “rewrite is easier” lemmas in a form usable by deterministic-next proofs:
    under `endpointSep`, the *interior* of a straight wall segment is disjoint from these
    half-spaces (`rwWall_false_disjoint_belowFlightLineLeft0_of_endpointSep` and the symmetric
    `rwWall_true_disjoint_belowFlightLineRight1_of_endpointSep`).
- `lean/HeytingLean/MirandaDynamics/Billiards/PaperReadWriteRewriteBetweenDeterministic.lean`
  - packages these half-space lemmas into a **segment-level** deterministic-first-hit proof
    (`Table.DeterministicNext.Good`) for a *rewrite between-wall flight* step, in a corridor-local
    setting where the boundary is:
      * the canonical straight-wall family at a fixed head index `k` and `cur`, with endpoint excluded;
      * the intended rewrite redirecting wall `tildeWallRewriteAppendix k ds cur`.
  - includes the explicit trajectory comparison lemma
    `RewriteBetween.hitPoint_mem_belowFlightLine` showing the whole flight segment stays in the
    read-only “below extremal line” half-space.
  - (Update) the straight-wall boundary is now the **full** canonical union over all head indices
    `rwWallUnionCanonicalNoEndpoint cur`, and the “hard” cross-`k` case uses the cross-`k`
    `endpointSepCross` inequalities already developed for the read-only Appendix proof.
  - (Update) the table normal is now piecewise: `rwWallNormal` on straight walls and
    `rwWallRewriteNormal` on the rewrite redirecting wall, so the computed `next?` reflects with
    the correct (perturbed-slope) normal at the actual first-hit point.

QA:

- `./scripts/qa_dev.sh --modules ...PaperReadWriteWallsRewriteAppendix ...PaperReadWriteFlightAvoidanceRewriteReduction ...PaperReadWriteRewriteBetweenDeterministic`
  passed (library-only changes).

### What is still open (remaining geometry / gluing)

1) **Cross-`k` rewrite avoidance**: extend the corridor-local deterministic step to a boundary union
   quantified over all head indices `k'` (the same scope as the straight Appendix step). The intent
   is to reuse the read-only cross-`k` inequalities already formalized for `flightRayLeft0` /
   `flightRayRight1`, but with the new half-space comparison layer.
2) **Full redirecting union**: upgrade the boundary from a single intended rewrite redirecting wall
   to the corresponding canonical union, proving “no earlier hit” against other redirecting walls.
3) **Global table/collision space + semiconjugacy**: glue the straight gadget step, rewrite gadget
   step, and (eventually) parabolic shift corridor into the collision-space `next?` needed for
   `GeometryToPaperTarget.PaperLink.semiconj` into `paperFctrl?`.

## Update (2026-01-19, later): redirecting-wall canonical union integrated

`PaperReadWriteRewriteBetweenDeterministic` now uses the fixed-`k` canonical union
`tildeWallRewriteAppendixUnionCanonicalAt e.k e.cur` in the table boundary, replacing the previous
single-wall `tildeWallRewriteAppendix e.k (ds e) e.cur`.

Key lemma (segment-level, minimal-time):
- `no_tildeWallRewriteAppendixUnionCanonicalAt_hit_before_two` shows the flight segment cannot hit
  **any** redirecting wall in this canonical union before time `2`. The proof uses a simple `y`
  bound: for any `tildeWallRewriteAppendix` point, `y ≤ rewriteSlope * rwBlockLen / 2`, while the
  between-wall trajectory satisfies `y = 2 + rewriteSlope*rwBlockLen/2 - t`, hence `t < 2` forces
  `y > rewriteSlope*rwBlockLen/2`.

This resolves item (2) for the corridor-local, fixed-head-index model. The remaining long-horizon
work is still (1) cross-`k` geometry and (3) the global collision-space glue into `paperFctrl?`.

## Update (2026-01-19, later): abstract “glue” lemma to `paperFctrl?`

New module:
- `lean/HeytingLean/MirandaDynamics/Billiards/GeometryToGenShiftCtrlLink.lean`

It formalizes the *reduction step* that the real WS7.3 geometry construction will use:
if a geometric collision cross-section `(Good, next?)` admits a decoding map
`decode : CollisionState → GenShiftCtrlCfg (Fin m) Bool` that commutes with one generalized-shift
step, then semiconjugacy to `paperFctrl?` follows automatically by composing with the already
mechanized WS7.4 semiconjugacy (`GenShiftCtrlPaperLink.lean`).

This does not solve the geometry itself, but it pins down the exact proof obligation the remaining
WS7.3 corridor gluing must discharge (“geometric return map simulates controlled generalized shift”).

## Update (2026-01-19, later): basic rewrite-redirecting disjointness lemma

`PaperReadWriteWallsRewriteAppendix.lean` now includes:
- `mem_tildeWallRewriteAppendix_iff_sub_shiftRewrite`
- `tildeWallRewriteAppendix_disjoint_of_length_eq`
- coarse strip bounds (`cur=false → x ≤ 0`, `cur=true → 1 ≤ x`) for rewrite-redirecting walls

These are the rewrite-redirecting analogues of the straight-gadget `tildeWall` interval-disjointness
lemmas: distinct blocks at the same `(k,cur)` yield disjoint rewrite-redirecting wall sets.

## Update (2026-01-19, later): canonical-length invariance + quantitative bounds (prep for cross-`k`)

`PaperReadWriteWallsRewriteAppendix.lean` now also records the “canonical length” consequences of
`rwDigits`:
- `rwBlockLen_eq_of_rwDigits`, `shiftRewrite_eq_of_rwDigits`, `rewriteSlope_eq_of_rwDigits`:
  for fixed `(k,cur)`, all canonical blocks `(pref++[cur])` share the same `rwBlockLen`, hence the
  same `shiftRewrite` and `rewriteSlope`.
- Stronger canonical-length bounds for later cross-`k` separation arguments:
  `rwBlockLen_le_headScale_div_ninth_of_rwDigits_neg` (`k < 0`) and
  `rwBlockLen_le_headScale_div_twentyseven_of_rwDigits_pos` (`0 < k`).
