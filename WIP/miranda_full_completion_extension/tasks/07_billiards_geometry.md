# WS7 Tasks: Billiard geometry (reflection law + trajectory semantics) (2026-01-17)

## Goal

Mechanize the **billiard dynamics** side of “classical billiards can compute”, building on the already
mechanized Cantor tape encoding spine:

- formal definition of billiard tables (at least a restricted class),
- specular reflection law at the boundary,
- trajectory evolution (map or flow),
- the computational encoding used by the paper,
- a Lean proof of the halting reduction to a billiard dynamical predicate.

## External references (primary)

- Miranda, Ramos, “Classical billiards can compute”.
  - arXiv:2512.19156: https://arxiv.org/abs/2512.19156

## Inputs (existing assets to reuse)

### In this repo
- Cantor encoding spine + head embedding:
  - `lean/HeytingLean/MirandaDynamics/Billiards/CantorEncoding.lean`
  - `lean/HeytingLean/MirandaDynamics/Billiards/CantorNucleus.lean`
- Undecidability-transfer layer:
  - `lean/HeytingLean/MirandaDynamics/Undecidability/Transfers.lean`
- Demo executable already present:
  - `miranda_billiards_demo` (smoke checks for encoding pieces)

## What’s missing / “no turnkey solution”

No ready-to-reuse Lean formalization of billiard reflection dynamics was found in initial searches.
Therefore we must design a staged formalization, likely starting with a restricted billiard class.

## Task list (decomposed)

### WS7.1 Decide a formal billiard model (Research-needed)

Key choice: what class of tables to formalize first?

Candidates:
- polygonal billiards (piecewise linear boundary): reflection is explicit and combinatorial,
- smooth strictly convex billiards (requires differential geometry),
- the exact paper’s billiard tables (likely piecewise smooth with obstacles).

We should start with the smallest model that can express the encoding skeleton.

**Acceptance:** a written decision with pros/cons and a mapping to required Mathlib dependencies.

Decision (2026-01-17): start with a **semantics-first** collision relation (not yet a unique billiard map).

- Pros:
  - avoids hard “next collision” existence/uniqueness/minimal-time proofs up front,
  - keeps the formalization usable for TKFT-style reachability and later reductions,
  - reuses Mathlib’s inner-product reflection to obtain invariants (involutive, norm-preserving).
- Cons:
  - not yet executable/computable, and not yet the classical billiard map,
  - needs later refinement to a restricted class (likely polygonal tables) to support the paper’s construction.
- Minimal Mathlib dependencies:
  - `Mathlib/Analysis/InnerProductSpace/Projection/Reflection.lean` (reflection),
  - `Mathlib/Analysis/Convex/Segment.lean` (segments for “flight stays inside”),
  - `Mathlib/Logic/Relation.lean` (reflexive-transitive closure).

### WS7.2 Define billiard table and reflection law (Complex)

- [x] Create `lean/HeytingLean/MirandaDynamics/Billiards/Geometry.lean`:
  - define table region `Ω ⊆ ℝ²` (or ℝ^n) with boundary regularity assumptions,
  - define valid collision points and inward normal / tangent,
  - define reflection map on velocity vectors (specular reflection).

**Acceptance:** a definitional layer that compiles and supports at least one nontrivial lemma
("reflection preserves speed", etc.).

### WS7.3 Define billiard dynamics as a map/flow (Complex)

- [ ] Choose discrete-time (billiard map from collision to collision) as the initial formal target.
- [ ] Define:
  - phase space (position on boundary + outgoing angle),
  - billiard map (next collision point + reflected velocity),
  - a reaching relation induced by iterating the map (can reuse `Flow.fromIter` pattern).

**Acceptance:** a “billiardReaches” predicate and a lemma that it composes/iterates correctly.

### WS7.4 Connect to Cantor encoding spine (Moderate → Complex)

- [ ] Identify where the paper’s encoding uses:
  - Cantor set membership,
  - head interval embedding,
  - symbolic dynamics / tape shifts.
- [ ] Prove the needed analytic lemmas that do not require full geometry.
- [ ] Then connect billiard map states to encoded tape states.

**Acceptance:** a Lean theorem linking a step of billiard dynamics to a step of encoded tape dynamics.

### WS7.5 Mechanize the halting reduction (Very Complex)

- [ ] Implement the mapping from halting instances to billiard instances.
- [ ] Prove correctness of the reduction.
- [ ] Derive non-computability via `Undecidability/Transfers`.

**Acceptance:** a theorem `haltingReducesToBilliardPredicate` in Lean, then a derived `not_computable_*` theorem.

### WS7.6 Executable-first: billiard sanity demo (Moderate)

- [x] Add a small executable that:
  - constructs a simple billiard table and runs a few discrete steps (pure arithmetic),
  - prints collision sequence / encoded digits, and exits 0.
- [x] Run robustness tests.

**Acceptance:** builds and runs under `env -i PATH=""` without crashing.

## QA protocol (incremental)

- Dev: `./scripts/qa_dev.sh --modules HeytingLean.MirandaDynamics`

## Progress log

- 2026-01-17:
  - Decision (WS7.1): start with a **semantics-first** billiard model that avoids “next collision”
    uniqueness/minimal-time issues:
    - a table given by `inside`/`boundary` sets and a chosen normal field on the boundary,
    - a one-step **collision semantics** `Step` (straight flight inside + specular velocity reflection),
    - reachability as a reflexive-transitive closure `Reaches`, plus a TKFT `ReachingRel` view.
    This is enough to state invariants and later connect to the Cantor-encoding spine, while keeping
    geometry-heavy choices (polygonal vs smooth tables) deferred.
  - Added a specular-reflection core based on Mathlib’s `Submodule.reflection`:
    - `lean/HeytingLean/MirandaDynamics/Billiards/SpecularReflection.lean`
      (`Billiards.reflect`, `Billiards.reflect_reflect`, `Billiards.norm_reflect`).
    - Extended test: `lean/HeytingLean/Tests/MirandaDynamics/BilliardsSanity.lean`.
  - Added a geometry skeleton (WS7.2/WS7.3 partial):
    - `lean/HeytingLean/MirandaDynamics/Billiards/Geometry.lean`
      (`Table`, `Table.Flight`, `Table.Step`, `Table.Reaches`, `Table.Step.norm_vel_eq`,
       `Table.reachingRel`, plus `Table.Reaches.refl/trans` and `Table.Step.reaches`).
  - Added a proof-grade unit-square table instance (staged):
    - `lean/HeytingLean/MirandaDynamics/Billiards/UnitSquare.lean`
      (`UnitSquare.region`, `UnitSquare.boundary`, `UnitSquare.convex_region`,
       `UnitSquare.segment_subset_region`, `UnitSquare.table`).
  - Added a runtime-only rectangle billiard demo (WS7.6):
    - `lean/HeytingLean/MirandaDynamics/Billiards/FloatSim.lean` (computable `Float` simulator)
    - `lean/HeytingLean/MirandaDynamics/Billiards/GeometryDemoMain.lean` + `miranda_billiards_geometry_demo`
    - Verified happy path + hostile env: `env -i PATH="" ./lean/.lake/build/bin/miranda_billiards_geometry_demo`.

- 2026-01-18:
  - WS7.3 (staged): added a **partial deterministic** “next collision” map on boundary states for the unit square:
    - `lean/HeytingLean/MirandaDynamics/Billiards/UnitSquareMap.lean`
      - `UnitSquareMap.next? : CollisionState → Option CollisionState`
      - `UnitSquareMap.Reaches : CollisionState → CollisionState → Prop`
      - `UnitSquareMap.Reaches_iff_exists_nextIter?` (reachability ↔ partial-iteration witness)
      - `UnitSquareMap.stepRel_to_tableStep` (soundness: map step ⇒ staged `UnitSquare.table.Step`)
    - Notes (still future work):
      - `next?` is currently staged as a partial map using a definitional `q ∈ boundary` check; later WS7.3
        work should prove totality/uniqueness on an explicit “good” phase space (excluding corners/tangency),
        and remove that check in favor of geometry lemmas.
  - WS7.4 (research/mapping): created a dedicated extraction + staging note:
    - `WIP/miranda_full_completion_extension/WS7_4_mapping_note_2026-01-18.md`
  - Cantor/head embedding upgrade (paper Lemma 1 packaging improvements):
    - `lean/HeytingLean/MirandaDynamics/Billiards/CantorEncoding.lean`:
      - `headShift`, `headShift_tau`
      - `tau_surj_headInterval`
      - `headShift_mem_headInterval_succ`

- 2026-01-19:
  - WS7.3 “glue target” factorization:
    - `lean/HeytingLean/MirandaDynamics/Billiards/GeometryToGenShiftCtrlLink.lean`:
      reduces the full geometric-to-paper semiconjugacy to a single obligation
      `decode_step : Option.map decode (next? s) = GenShiftCtrlMap.next? … (decode s)` on `Good` states.
  - Rewrite-redirecting prep for cross-`k` (canonical bounds + invariance under `rwDigits`):
    - `lean/HeytingLean/MirandaDynamics/Billiards/PaperReadWriteWallsRewriteAppendix.lean`:
      - canonical-length invariance: `rwBlockLen_eq_of_rwDigits`, `shiftRewrite_eq_of_rwDigits`,
        `rewriteSlope_eq_of_rwDigits`,
      - quantitative bounds (useful for head-interval separation): `rwBlockLen_le_headScale_div_ninth_of_rwDigits_neg`,
        `rwBlockLen_le_headScale_div_twentyseven_of_rwDigits_pos`,
      - explicit canonical-length form: `rwBlockLen_eq_headScale_mul_inv_pow_indexNat_succ`.
  - WS7.3 table/collision-space scaffold for the full read–write gadget boundary union:
    - `lean/HeytingLean/MirandaDynamics/Billiards/PaperReadWriteTableCanonical.lean`:
      defines the canonical boundary union + a collision-space `CollisionState` + deterministic `next?`
      (still missing: “Good → defined/unique/no-spurious” and the semiconjugacy proof).
  - WS7.3 (staged): global rewrite-redirecting union refactor for the rewrite between-wall step:
    - `lean/HeytingLean/MirandaDynamics/Billiards/PaperReadWriteRewriteBetweenDeterministicGlobal.lean`:
      defines a rewrite-between table whose boundary uses the **global** rewrite-redirecting canonical union
      (across all head indices), and packages deterministic-first-hit + `next?` computation under an explicit
      hypothesis `NoOtherKRedirectingHitsBeforeTwo` isolating the remaining cross-`k` redirecting-wall
      avoidance lemma.
  - WS7.3: discharged the cross-`k` rewrite-redirecting avoidance gap and removed the staging hypothesis layer:
    - `lean/HeytingLean/MirandaDynamics/Billiards/PaperReadWriteRewriteBetweenDeterministicGlobal.lean`:
      proved `RewriteBetweenGlobal.noOtherKRedirectingHitsBeforeTwo`, and exposed the global-boundary corridor step
      as `RewriteBetween.tableGlobal` + `RewriteBetween.next?_eq_some_global`.
  - Rewrite-between support lemma exposure:
    - `lean/HeytingLean/MirandaDynamics/Billiards/PaperReadWriteRewriteBetweenDeterministic.lean`:
      made `y_le_rewriteSlope_mul_half_rwBlockLen_of_mem_tildeWallRewriteAppendix` non-private so the
      cross-`k` rewrite-redirecting avoidance proof can reuse the same wall `y`-bounds without duplication.
  - Parabolic shift corridor (WS7.3 core): deterministic minimal-time collision theorems for the two-parabola gadget:
    - `lean/HeytingLean/MirandaDynamics/Billiards/ParabolicShiftCorridorDeterministic.lean`:
      - proves `Table.DeterministicNext.Good` and computes `next?` for:
        - the first parabola hit at time `1`,
        - the second parabola hit at time `hitTime₂` with “no earlier hit” in the corridor regime `f₂/f₁ < 1`,
      - provides a two-bounce wrapper `next2?` with `next2?_eq_some_hit₂`,
      - exposes the induced affine update on the `x` coordinate (`x_hit₂_eq_affineUpdate`)
        and a vertical-outgoing-velocity lemma (`hit₂_vel_is_vertical`).
  - WS7.3 glue staging note:
    - `WIP/miranda_full_completion_extension/WS73_glue_next_sprint_note_2026-01-19.md`:
      records the next mechanizable phase (macro return-step model + `decode_step`) and the
      remaining hard geometry blockers for a true global table/cross-section return map.
