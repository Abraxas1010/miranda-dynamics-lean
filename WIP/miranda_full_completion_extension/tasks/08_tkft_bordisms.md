# WS8 Tasks: TKFT “clean dynamical bordisms” (structure + gluing) (2026-01-17)

## Goal

Fully mechanize a Lean notion of the TKFT “clean dynamical bordism” from the TKFT paper(s), including:

- a definition of the bordism object/morphism,
- a gluing operation (composition),
- a theorem that the induced reaching semantics composes via relational composition.

This WS is attractive because it can progress **without** waiting for PDE infrastructure, by:
- starting with discrete/PL analogues,
- proving the semantics law abstractly,
- then refining the definition toward the paper’s smooth “clean bordism” hypotheses.

## External references (primary)

- González-Prieto, Miranda, Peralta-Salas, “Topological Kleene Field Theories as a model of computation”.
  - arXiv:2503.16100: https://arxiv.org/abs/2503.16100

## Inputs (existing assets to reuse)

### In this repo
- Reaching relations + composition laws:
  - `lean/HeytingLean/MirandaDynamics/TKFT/Reaching.lean`
- Category packaging:
  - `lean/HeytingLean/MirandaDynamics/TKFT/Category.lean`
  - `lean/HeytingLean/MirandaDynamics/TKFT/RelCatBridge.lean` (equivalence to Mathlib `RelCat`)
- Flow reaching (global flows):
  - `lean/HeytingLean/MirandaDynamics/TKFT/FlowReaching.lean`

## What’s missing / “no turnkey solution”

There is no existing “clean dynamical bordism” formalization in this repo, and no ready-to-use Lean library
was identified in initial searches.

So we proceed by staged formalization:

1) **Abstract semantics-first** (define a structure whose semantics is a reaching relation), then  
2) **Concrete model(s)** (discrete, then smooth), then  
3) **Paper alignment** (tighten hypotheses to match TKFT definitions).

## Task list (decomposed)

### WS8.1 Extract definitions + gluing axioms from the paper (Research-needed)

- [ ] Identify the exact paper definition of “clean dynamical bordism”:
  - underlying manifold/space,
  - boundary decomposition,
  - dynamical structure (flow / vector field),
  - “clean” conditions (transversality? regular values?).
- [ ] Identify the statement of the “gluing” theorem and the semantic reaching-function theorem.

**Acceptance:** a precise list of required definitions and theorem statements written in this file.

### WS8.2 Define an abstract `BordismSemantics` interface (Moderate)

Create a small structure that captures only what later proofs need:

```lean
structure BordismSemantics (In Out : Type*) where
  reach : ReachingRel In Out
```

Then define gluing as composition at the semantics level and prove category laws.

**Acceptance:** a “semantics-only” category with proofs, no sorries.

### WS8.3 Implement a discrete bordism model (Moderate → Complex)

Use a discrete model where the “bordism” is a state transition system with designated in/out boundaries:

- [x] Define a discrete bordism:
  - state space `S`,
  - entry boundary `In`, exit boundary `Out`,
  - evolution step (or flow via `Flow.fromIter`).
- [x] Define its induced reaching relation.
- [x] Prove gluing semantics corresponds to `ReachingRel.comp`.

**Acceptance:** end-to-end proof for the discrete model.

### WS8.4 Refine toward a smooth model (Research-needed → Complex)

Once WS1 provides a partial-flow abstraction:

- [ ] Define a “dynamical bordism” as:
  - a space `M` with subsets `In Out`,
  - a partial flow `ϕ`,
  - hypotheses ensuring gluing works.
- [ ] Prove the semantic law using WS1 `PartialFlowReaching`.

**Acceptance:** a smooth/ODE-flavored bordism definition with the semantic composition theorem.

### WS8.5 Align to TKFT “clean” hypotheses (Very Complex)

This is where the paper-specific geometry enters:

- [ ] replace abstract hypotheses with the paper’s “clean” conditions,
- [ ] prove the abstract hypotheses from the clean conditions.

**Acceptance:** “clean dynamical bordism ⇒ semantics glues” as a Lean theorem.

## QA protocol (incremental)

- Dev: `./scripts/qa_dev.sh --modules HeytingLean.MirandaDynamics`

## Progress log

- 2026-01-17: Implemented semantics-first + discrete gluing model.
  - New: `lean/HeytingLean/MirandaDynamics/TKFT/BordismSemantics.lean` (semantics-only bordisms + category).
  - New: `lean/HeytingLean/MirandaDynamics/TKFT/DiscreteBordism.lean` (discrete bordism + `glue`; theorem
    `DiscreteBordism.reachingRel_glue_eq_comp`).
  - New test: `lean/HeytingLean/Tests/MirandaDynamics/TKFTBordismSanity.lean`.
  - QA: `./scripts/qa_dev.sh --modules HeytingLean.MirandaDynamics` and `./scripts/qa_robustness_affected.sh --modules HeytingLean.MirandaDynamics`.
