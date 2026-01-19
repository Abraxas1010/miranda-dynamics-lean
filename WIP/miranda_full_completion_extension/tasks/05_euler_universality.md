# WS5 Tasks: Euler universality construction (2026-01-17)

## Goal

Replace the current “external claim” wrapper for Euler universality with a fully mechanized Lean development:

- define the Euler steady-state object(s) used in the universality construction,
- mechanize the construction showing a halting reduction to a dynamical predicate for Euler flows,
- derive non-computability using the already-mechanized undecidability-transfer layer.

This is the highest-risk workstream: it depends on WS1 (flows), WS2 (forms), WS3 (contact/Reeb), WS4 (Beltrami/Euler).

## External references (primary)

- Cardona, Miranda, Peralta-Salas, Presas, “Universality of Euler flows and flexibility of Reeb embeddings”.
  - arXiv:1911.01963: https://arxiv.org/abs/1911.01963
  - PNAS: https://www.pnas.org/doi/10.1073/pnas.2026818118

## Inputs (existing assets to reuse)

### In this repo
- Undecidability-transfer spine:
  - `lean/HeytingLean/MirandaDynamics/Undecidability/Transfers.lean`
- External claim wrapper (to eventually delete/retire):
  - `lean/HeytingLean/MirandaDynamics/External/Claims.lean`
  - `lean/HeytingLean/MirandaDynamics/External/Consequences.lean`

## What’s missing / “no turnkey solution”

- There is no existing Lean formalization of the Euler universality construction in this repo, and no
  ready-to-reuse Lean library was found in initial external searches.

Therefore WS5 must be decomposed into narrow, defensible milestones.

## Task list (decomposed)

### WS5.1 Formal statement audit (Research-needed)

- [x] Extract the *exact* theorem statements needed for the reduction step from the paper(s):
  - input computational model: (reversible) Turing machines via Moore-style generalized shifts.
  - intermediate dynamics: generalized shifts → piecewise-linear Cantor-block maps → smooth disk diffeomorphisms.
  - geometric bridge: disk diffeo as Reeb return map (Theorem 3.1 in the PNAS paper).
  - hydrodynamic bridge: Reeb ↔ (rotational) Beltrami ↔ stationary Euler (Theorem 2.1 in the PNAS paper).
  - target dynamical predicate: existence of an orbit intersecting a chosen open set `U` (reachability / visiting).
  - regularity assumptions: smooth (`C^∞`) dynamics on compact manifolds; Eulerisable/Beltami hypotheses.
- [x] Record the statements “as Lean propositions” in this task file (not as axioms in code).

#### WS5.1 Evidence + target statements (2026-01-18)

Primary source used for statement extraction:
- Cardona–Miranda–Peralta-Salas–Presas, “Constructing Turing complete Euler flows in dimension 3”
  (PNAS 2021; full text on PMC): https://pmc.ncbi.nlm.nih.gov/articles/PMC8126859/

Key statements (informal, but structured for Lean translation):

1) Generalized shifts encode Turing machines (Lemma 4.4).
- Given a Turing machine `T`, there exists a generalized shift `φ` on `Σ^ℤ` and an injective encoding `ι`
  such that one step of `T` corresponds to one application of `φ` on encoded configurations.

Lean-facing shape (target):
- define `GeneralizedShift Σ` (data: finite window size + local update rule + head-move rule),
- define “conjugated” to a `HaltSys` or TM transition system by an injective `ι` with `ι (step c) = φ (ι c)`.

2) Generalized shifts ↔ Cantor-block maps (Lemma 4.7).
- Any generalized shift is conjugated to the restriction to the square Cantor set of a piecewise linear
  map of `[0,1]^2`, built from finitely many affine components on Cantor blocks; bijective shifts give
  pairwise disjoint image blocks.

Lean-facing shape (target):
- define a “Cantor block” structure (products of basic Cantor intervals),
- define a piecewise-affine map on `[0,1]^2` with proofs:
  - preserves the Cantor set,
  - agrees with generalized shift under the conjugacy.

3) Disk diffeomorphism realizing the Cantor dynamics (Proposition 5.1 + Theorem 5.2).
- Proposition 5.1: For each bijective generalized shift and its Cantor-block map `φ`, there exists an
  area-preserving diffeomorphism `ψ : D → D` (identity near ∂D) whose restriction to the square Cantor
  set is conjugated to `φ`.
- Theorem 5.2: There exists a Turing complete area-preserving diffeomorphism of the disk, identity near
  the boundary.

Lean-facing shape (target):
- This is currently far beyond Mathlib; treat as a long-horizon mechanization target.
- For the reduction, the minimal interface is: an explicit smooth map `ψ : D → D` plus a proven
  simulation relation from the discrete halting model to `ψ`-reachability of an open set.

4) Contact mirror / Reeb–Beltrami correspondence (Theorem 2.1).
- Any nonvanishing rotational Beltrami field is a reparametrization of a Reeb vector field for some
  contact form; conversely, any reparametrization of a Reeb vector field is a nonvanishing rotational
  Beltrami field for some Riemannian metric and volume form.

Lean-facing shape (target):
- define (Euclidean-first, then manifold) “Beltrami field” and “Reeb field” predicates,
- prove the correspondence under explicit hypotheses (nonvanishing, coorientable contact structure, …).

5) Turing complete Eulerisable flow (Theorem 6.1).
- There exists an Eulerisable flow `X` on `S^3` that is Turing complete in the reachability sense:
  for any `k`, given a Turing machine `T`, an input tape `t`, and a finite output pattern
  `(t*_{-k}, …, t*_{k})`, there exist a constructible point `p` and open set `U` such that the orbit of
  `X` through `p` intersects `U` iff `T` halts with an output tape matching that pattern on `[-k,k]`.

Lean-facing shape (target):
- represent “orbit intersects open set” via a `ReachingRel` / `Flow` reachability predicate,
- connect “halts with output pattern” to reachability of a set of encoded states (already done in the
  discrete spine for `Nat.Partrec.Code`; needs a TM↔Partrec bridge or a TM formalization).

**Acceptance:** a clean list of target theorems with hypotheses, plus a mapping to planned Lean definitions.

### WS5.2 Minimal Euler steady-state definitions (Complex)

- [ ] Decide the domain:
  - start with ℝ³ or a simple compact manifold (e.g. 3-torus) if Mathlib supports it well.
- [ ] Define Euler steady state in the chosen formalism (vector calculus or differential forms).

**Acceptance:** ability to state “u is a steady Euler flow on M” as a Lean predicate.

### WS5.3 Reeb embedding sub-bridge (Research-needed → Complex)

The Euler universality construction uses a bridge between Reeb flows and Euler flows.

- [ ] Identify the minimum mechanization needed:
  - definitions of Reeb flow from contact form (WS3),
  - embedding statement(s),
  - transformation of dynamics preserving the reduction predicate.
- [ ] Mechanize the simplest nontrivial lemma in that bridge (to validate the approach).

**Acceptance:** one “bridge lemma” proved in Lean, with a clear dependency list.

### WS5.4 Encode computation and prove the reduction (Very Complex)

- [ ] Choose an internal computational model to target:
  - reuse existing `Nat.Partrec.Code` halting model already used in the discrete bridge, if possible.
- [ ] Implement the reduction mapping:
  - from a halting instance to an Euler predicate instance.
- [ ] Prove correctness of the reduction (both directions required for “iff” style claims; one direction
  may suffice for noncomputability transfer depending on the target).

**Acceptance:** a Lean theorem `haltingReducesToEulerPredicate` (many-one) without sorries.

### WS5.5 Replace external claim usage (Moderate)

- [ ] Once WS5.4 exists, update:
  - `External/Claims` and `External/Consequences` to either:
    - delete the Euler external claim, or
    - mark it as “superseded by mechanization” and route the consequence through the mechanized proof.

**Acceptance:** no downstream modules rely on the Euler external claim wrapper for results now mechanized.

## QA protocol (incremental)

- Dev mode continuously: `./scripts/qa_dev.sh --modules HeytingLean.MirandaDynamics`
- Add a small Euler-related `lean_exe` only after core definitions stabilize.

## Progress log

- 2026-01-17: (placeholder) Task file created.

- 2026-01-18:
  - WS5.1 statement audit recorded above (PNAS full text on PMC).
  - WS5.2 (Euclidean staging already exists in code; not yet manifold-level):
    - `lean/HeytingLean/MirandaDynamics/Fluids/VectorCalculus/Curl3.lean`:
      - `Fluids.VectorCalculus.R3.curl`
      - `Fluids.VectorCalculus.R3.IsBeltrami`
    - `lean/HeytingLean/MirandaDynamics/Fluids/VectorCalculus/GradDiv3.lean`:
      - `Fluids.VectorCalculus.R3.IsEulerSteadyBernoulli` (Lamb/Bernoulli shell `u × curl u = ∇p`)
      - `Fluids.VectorCalculus.R3.eulerSteadyBernoulli_const_of_beltrami`
    - Remaining gap for WS5.2: replace/augment this with a manifold-level Euler predicate suitable for
      the paper’s `S^3` construction (requires WS2/WS3/WS4 infrastructure).
