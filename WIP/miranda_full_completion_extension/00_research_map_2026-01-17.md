# Research Map: “Full Completion” extension (2026-01-17)

This note is the **research-first evidence log** for the “full completion” project extension.
It complements (does not replace) `WIP/miranda_research_map_2026-01-17.md`, which documents the already
mechanized MirandaDynamics spine.

## 0) Scope and truthfulness rules

This repo currently has a **Lean-realistic spine** (reaching relations, nuclei, discrete reduction, Cantor encoding)
that is fully mechanized. “Full completion” means mechanizing the geometry/PDE constructions too.

This research map records:
- what Mathlib already provides (to reuse),
- what is missing (to build),
- external references (papers/texts),
- external formalizations (Lean first; then other provers).

## 1) Primary literature (Miranda ecosystem)

- TKFT:
  - González-Prieto, Miranda, Peralta-Salas, “Topological Kleene Field Theories as a model of computation”.
  - arXiv:2503.16100: https://arxiv.org/abs/2503.16100

- Billiards:
  - Miranda, Ramos, “Classical billiards can compute”.
  - arXiv:2512.19156: https://arxiv.org/abs/2512.19156

- Euler flows universality:
  - Cardona, Miranda, Peralta-Salas, Presas, “Universality of Euler flows and flexibility of Reeb embeddings”.
  - arXiv:1911.01963: https://arxiv.org/abs/1911.01963
  - PNAS paper: “Constructing Turing complete Euler flows in dimension 3” (PNAS 118(19):e2026818118):
    https://www.pnas.org/doi/10.1073/pnas.2026818118

- Navier–Stokes steady states universality:
  - Dyhr, González-Prieto, Miranda, Peralta-Salas, “Turing complete Navier-Stokes steady states via cosymplectic geometry”.
  - arXiv:2507.07696: https://arxiv.org/abs/2507.07696
  - Related cosymplectic/Reeb title (same author, different claim focus):
    https://arxiv.org/abs/2505.10379

## 2) Foundational references (definitions and background)

These are used to align *definitions* (contact/cosymplectic/Beltrami), not as proof sources.

- Contact topology notes:
  - John B. Etnyre, “Lectures on Contact Geometry in Low-Dimensional Topology” (2003, updated versions exist):
    https://math.gatech.edu/~etnyre/preprints/LectureNotes.pdf
  - Quick definition cross-check (non-authoritative, but convenient pointer):
    https://en.wikipedia.org/wiki/Reeb_vector_field

- Classical fluids/geometry background (Beltrami/Euler context):
  - Arnold & Khesin, “Topological Methods in Hydrodynamics” (Springer; reference landing page):
    https://link.springer.com/book/10.1007/978-1-4757-2135-4

## 3) Mathlib capability scan (what we can reuse)

### 3.1 ODE / integral curves / (local) flows

Internal repo scan confirms Mathlib has substantial ODE and manifold integral-curve machinery:
- `Mathlib/Analysis/ODE/PicardLindelof.lean` (Picard–Lindelöf; local solutions; local flow existence).
- `Mathlib/Geometry/Manifold/IntegralCurve/ExistUnique.lean` (integral curve existence/uniqueness on manifolds).

Online references (for stable links and context):
- Mathlib docs: Picard–Lindelöf:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/ODE/PicardLindelof.html
- Mathlib docs: integral curves (definitions):
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/IntegralCurve/Basic.html
- Mathlib docs: integral curves on manifolds (exist/unique):
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/IntegralCurve/ExistUnique.html
- Mathlib docs: vector fields on manifolds (pullbacks, Lie bracket pointers):
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/VectorField/Pullback.html

Implication: WS1 (smooth flows & reaching) should be **reuse-first**, not built from scratch.

Additional internal scan (Jan 2026):
- There does not appear to be a standalone `structure LocalFlow` / `PartialFlow` abstraction in Mathlib
  that directly packages a domain predicate plus the time-addition law. The Picard–Lindelöf development
  instead provides “local flow” as a function `α : E → ℝ → E` together with theorems about derivatives
  on a specified neighborhood domain.

### 3.2 Differential forms (on normed spaces)

Mathlib provides differential forms and exterior derivative on normed spaces:
- `Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`

Online reference:
- Mathlib docs: exterior derivative of a differential form on a normed space:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/DifferentialForm/Basic.html

Gap: there is no clear, ready-to-use manifold differential-form layer in the local scan. WS2 must either:
1) build a manifold-form wrapper (chart-based), or
2) develop the needed geometry in Euclidean spaces first, then generalize.

### 3.3 Contact/cosymplectic/Beltrami (negative results)

Internal scan did **not** find Mathlib modules providing:
- contact structures / Reeb vector fields,
- cosymplectic geometry,
- Beltrami fields or vector-calculus “curl” API usable for Euler steady states.

This is consistent with the earlier backlog note, but updated with a positive finding:
the ODE/integral-curve layer *does* exist; the contact/cosymplectic layer does not.

### 3.4 Contact (Euclidean staging in this repo)

Given the missing turnkey manifold-contact library, we stage the contact story as:

- Differential-form-facing pointwise predicates on a normed space `E`:
  - `HeytingLean.MirandaDynamics.Geometry.Contact.NondegKer` (kernel nondegeneracy surrogate)
  - `HeytingLean.MirandaDynamics.Geometry.Contact.IsReebAt` (Reeb equations `α(R)=1` and `dα(R,·)=0`)
  - `HeytingLean.MirandaDynamics.Geometry.Contact.reeb_unique_of_nondegKer` (uniqueness under `NondegKer`)
  - implemented in `lean/HeytingLean/MirandaDynamics/Geometry/Contact/Euclidean.lean`
- These predicates use Mathlib’s exterior derivative `extDeriv` (via `Geometry.Forms.d`) and
  the currying/multilinearity API for continuous alternating maps (`ContinuousAlternatingMap.curryLeft`,
  `ContinuousAlternatingMap.vecCons_add`, `ContinuousAlternatingMap.vecCons_smul`).

Definition cross-check sources:
- Etnyre lecture notes (Reeb equations): https://math.gatech.edu/~etnyre/preprints/LectureNotes.pdf
- Mathlib docs for `extDeriv`: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/DifferentialForm/Basic.html
- Convenience pointer: https://en.wikipedia.org/wiki/Reeb_vector_field

### 3.5 Vector calculus staging (curl/Beltrami)

For the Euler/Beltrami path (WS4/WS5), Mathlib in this repo does not expose a ready-made `curl`.
We therefore staged a coordinate definition on `ℝ³ := Fin 3 → ℝ` using `fderiv`:

- `HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3.curl`
- `HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3.IsBeltrami`
- implemented in `lean/HeytingLean/MirandaDynamics/Fluids/VectorCalculus/Curl3.lean`

We also staged a “steady Euler (Bernoulli/Lamb form) shell” and proved the minimal implication
needed downstream:

- `HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3.IsEulerSteadyBernoulli`
  - definition: `u × curl u = ∇p` pointwise
  - implemented in `lean/HeytingLean/MirandaDynamics/Fluids/VectorCalculus/GradDiv3.lean`
- `HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3.eulerSteadyBernoulli_const_of_beltrami`
  - proof uses only linearity of the cross product and `Mathlib.LinearAlgebra.CrossProduct.cross_self`
  - implemented in `lean/HeytingLean/MirandaDynamics/Fluids/VectorCalculus/GradDiv3.lean`

Definition cross-check source (coordinate formula):
- Wikipedia (curl): https://en.wikipedia.org/wiki/Curl_(mathematics)
Background cross-check sources (Bernoulli/Lamb form; Beltrami fields):
- Wikipedia (Lamb form of Euler): https://en.wikipedia.org/wiki/Euler_equations_(fluid_dynamics)
- Wikipedia (Beltrami flow; Lamb vector vanishes): https://en.wikipedia.org/wiki/Beltrami_flow
- Mathlib docs (cross product; `cross_self`): https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/CrossProduct.html
- Berger–Florio–Peralta-Salas, “Steady Euler flows on R^3 with wild and universal dynamics” (Beltrami steady solutions):
  https://arxiv.org/abs/2202.02848
- Cardona–Miranda–Peralta-Salas, “Computability and Beltrami fields in Euclidean space” (Beltrami type stationary Euler flows):
  https://arxiv.org/abs/2111.03559

Internal scan note (Mathlib pin in this repo): a search for `Hodge`/`hodge`/`HodgeStar`/`hodgeStar`
did not find a general Hodge-star operator for alternating forms; orientation/volume-form infrastructure
exists (e.g. `Orientation.volumeForm` in `Mathlib/Analysis/InnerProductSpace/TwoDim.lean`), but the full
“`curl` via `⋆ d`” path remains a future integration task.

### 3.6 Billiards: specular reflection (inner-product core)

For billiard geometry (WS7), we stage the reflection law using Mathlib’s inner-product-space reflection
in a subspace:

- Mathlib provides `Submodule.reflection : E ≃ₗᵢ[𝕜] E` (a linear isometry equivalence), with involutivity and
  norm preservation lemmas in `Mathlib/Analysis/InnerProductSpace/Projection/Reflection.lean`.
- We use it to define specular reflection across the tangent hyperplane `((ℝ ∙ n)ᗮ)` for a normal vector `n`.

Implemented in this repo:
- `HeytingLean.MirandaDynamics.Billiards.reflect`
- `HeytingLean.MirandaDynamics.Billiards.reflect_reflect`
- `HeytingLean.MirandaDynamics.Billiards.norm_reflect`
- `HeytingLean.MirandaDynamics.Billiards.reflect_normal_eq_neg`
- in `lean/HeytingLean/MirandaDynamics/Billiards/SpecularReflection.lean`

Trajectory semantics (staged; no “next collision” uniqueness yet):
- `HeytingLean.MirandaDynamics.Billiards.Table`
- `HeytingLean.MirandaDynamics.Billiards.Table.Flight`
- `HeytingLean.MirandaDynamics.Billiards.Table.Step`
- `HeytingLean.MirandaDynamics.Billiards.Table.Reaches`
- `HeytingLean.MirandaDynamics.Billiards.Table.Step.norm_vel_eq`
- `HeytingLean.MirandaDynamics.Billiards.Table.reachingRel`
- in `lean/HeytingLean/MirandaDynamics/Billiards/Geometry.lean`

Definition cross-check sources:
- Mathlib docs (reflection): https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Projection/Reflection.html
- Wikipedia (specular reflection law): https://en.wikipedia.org/wiki/Specular_reflection
- Tabachnikov, “Geometry and Billiards” (reflection law + billiard map background):
  https://bookstore.ams.org/surv-30

Internal scan note (Mathlib pin in this repo): a grep/ripgrep scan for “billiard(s)” in Mathlib
did not turn up an existing billiard-map library; we therefore proceed with a project-local staged
formalization (reflection core + reachability semantics).

## 4) External formalizations scan (Lean first; then other provers)

### 4.1 Lean / Mathlib

Searches (Jan 2026) for Lean formalizations of:
- contact geometry / Reeb vector field,
- cosymplectic geometry,
- billiards reflection law and trajectory semantics,
- cobordism categories / TQFT-like bordism categories,
did not yield a ready-to-reuse verified library beyond the ODE/integral-curve and differential-form-on-normed-space
components listed above.

Search terms used (non-exhaustive):
- “Lean contact geometry Reeb vector field Mathlib”
- “Lean cosymplectic geometry formalization”
- “Lean billiards reflection law formalization”
- “Lean cobordism category”
- “Mathlib cobordism”
- “Lean TQFT bordism category”
- “Mathlib local flow Picard Lindelöf structure”
- “Mathlib hodgeStar / Hodge star operator”

Search outcome note:
- We found Mathlib documentation and source for ODE/integral-curve foundations (Section 3.1), but did not find
  a pre-existing general-purpose local-flow structure with the exact algebraic interface needed for TKFT-style
  reachability; this motivates the project-local `Dynamics.PartialFlow` packaging.
- We did not find a verified Lean library providing the geometric cobordism-category structures one would use
  for a TQFT implementation; this motivates the semantics-first `TKFT.BordismSemantics` layer in this repo.
- For differential forms, Mathlib provides `extDeriv` and `extDerivWithin` on normed spaces, but (in this repo’s
  Mathlib pin) does not provide a bundled manifold-level exterior derivative; Mathlib’s own file comments note
  that the manifold analogue is “not defined yet”. We therefore use Euclidean-first forms and the “within a set”
  surrogate `Forms.dWithin` for chart-local staging.
  - Mathlib docs: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/DifferentialForm/Basic.html

### 4.2 Other provers (Coq/Isabelle/Agda)

Initial scan did not identify a “drop-in” billiards/contact/cosymplectic formalization for direct porting.
If/when a specific library is found later, we will add it here with:
- a stable link,
- the core definitions it provides,
- a mapping plan to Lean.

## 5) Decision: where to start

Based on reuse potential and dependency structure:

1. Start WS1 (flows & reaching) by packaging Mathlib’s ODE/integral-curve results into a Lean API that can feed
   the existing `TKFT.reachingRelOfFlow` story (likely via a **partial flow** notion).
2. Then WS2 (forms) → WS3 (contact) to create a geometric foundation for the Euler/Navier–Stokes tracks.
3. Run billiards (WS7) and TKFT bordisms (WS8) as parallel “geometry semantics” efforts that can proceed
   without waiting for PDE infrastructure.

---

## 6) Update log (2026-01-18)

### 6.1 Unit-square “next collision” map (formalization context)

External search focus: existing *verified* formalizations (Lean/Mathlib first) for:
- ray/line intersection with an axis-aligned rectangle (unit square),
- “next boundary hit” in convex sets / polytopes,
- billiard map implementations.

Outcome:
- No ready-to-reuse Lean/Mathlib formalization of a billiard map or “next collision” operator was found.
- For algorithmic guidance (non-verified, but standard references), the ray–AABB intersection “slab method”
  is documented in:
  - PBRT v4 (Ray–Box intersection section):
    https://pbr-book.org/4ed/Shapes/Ray_Intersections#RayBoxIntersection
  - Ray Tracing Gems II (Fast, Branchless Ray/Bounding Box Intersections):
    https://www.realtimerendering.com/raytracinggems/rtg2/index.html

Lean mapping note:
- For WS7.3 we continue with an **explicit-coordinate**, `ℝ`-based approach for the unit square
  (case splits on velocity signs; min-time to the next wall), with corner/tangency excluded as a
  later refinement target.
