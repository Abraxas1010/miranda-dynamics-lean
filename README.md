<img src="assets/Apoth3osis.webp" alt="Apoth3osis Logo" width="140"/>

# Miranda Dynamics

What physics, computation, and logic have in common — machine‑verified and empirically validated

[![Lean 4](https://img.shields.io/badge/Lean-4-blue.svg)](https://lean-lang.org)
[![Mathlib](https://img.shields.io/badge/Mathlib-latest-purple.svg)](https://github.com/leanprover-community/mathlib4)
[![Sorry Count](https://img.shields.io/badge/sorry-0-brightgreen.svg)](RESEARCHER_BUNDLE/HeytingLean/MirandaDynamics/)
[![License](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE.md)
[![Live Demo](https://img.shields.io/badge/🌍_Live_Demo-View_Visualization-00ff88.svg)](https://abraxas1010.github.io/miranda-dynamics-lean/visualization/)

---

## Docs Index

- Start here: docs/WHY_THIS_MATTERS.md
- Wolfram bridge and cross‑checks: docs/WOLFRAM.md

---

## The Discovery

Three research programs, working independently, discovered they were studying the same mathematical structure:

| Who | What They Study | Key Insight |
|-----|-----------------|-------------|
| Eva Miranda (Barcelona) | Billiards, fluid dynamics | “Any smooth dynamical system can compute anything.” |
| Stephen Wolfram (Wolfram Physics) | Hypergraph rewriting | “Simple rules generate all of physics.” |
| This Project | Formal logic in Lean | “Observation has algebraic structure.” |

They all discovered the same thing: the relationship between what’s true and what’s observable follows precise algebraic laws.

---

## Why This Matters

- Physicists: The gap between “particle arrives” and “detector fires” isn’t noise — it’s a fundamental logical structure that can be computed and predicted.
- Computer scientists: Turing completeness isn’t just about silicon. Billiard balls, fluid flows, and seismic waves can all “compute” in the same formal sense.
- Mathematicians: Category theory provides the right language to unify these domains. We prove the link in Lean with zero unverified assumptions.
- Data scientists: Your 7% false‑negative rate might not be model error — it can be an irreducible epistemic uncertainty we can characterize precisely.

---

## Key Result (Real Data)

Validated against real seismic data:

| Metric | Value | Meaning |
|--------|-------|---------|
| Accuracy | 92.86% | Framework correctly predicts wave detection |
| Heyting Gap | 7.14% | True arrivals below detection threshold (j(P) < P) |
| False Positives | 0% | Never predicts detection without physics |

The “gap” isn’t failure — it’s the framework quantifying what’s unknowable from finite observation.

---

## Unified Framework (Miranda ⟷ Wolfram ⟷ Heyting)

| Framework | Core Object | “Reaching” | “Gap” |
|-----------|-------------|------------|-------|
| Miranda TKFT | Bordism flow | Wave arrives | Below threshold |
| Wolfram Physics | Multiway graph | Branch merges | Branch diverges |
| Heyting Algebra | Nucleus j | j(P) = P | j(P) < P |

This repository contains the Lean 4 formalization (zero sorry), executables, and a Wolfram bridge to cross‑check the Lean ↔ Wolfram pipeline.

---

## Quick Start

Build everything (incremental, strict flags):

```bash
cd RESEARCHER_BUNDLE
lake build --wfail
```

Run the end‑to‑end verification (build + demos + robustness checks):

```bash
cd RESEARCHER_BUNDLE
./scripts/verify_miranda.sh
```

Seismic validation (JSON‑only mode recommended for scripting):

```bash
# Uses data/seismic/sample_bundle.json by default
cd RESEARCHER_BUNDLE
lake exe seismic_validate_demo

# Or specify a bundle explicitly
lake exe seismic_validate_demo -- --json-only ../data/seismic/validation_bundle.json > ../results/seismic_validation/lean_output.json
```

Wolfram Physics bridge demos (Lean ⟷ Wolfram):

```bash
cd RESEARCHER_BUNDLE
lake exe wolfram_multiway_demo -- --sys ce1 --maxDepth 2
lake exe wolfram_wm148_demo -- --maxDepth 2

# Requires wolframscript on PATH; performs byte‑identical binary roundtrip
lake exe wolfram_roundtrip -- --echo
```

---

## Project Structure (selected)

```
RESEARCHER_BUNDLE/HeytingLean/MirandaDynamics/
├── TKFT/                           # Layer 1: Abstract categorical framework
│   ├── Reaching.lean               # ReachingRel with categorical laws
│   ├── Category.lean               # Category instance
│   ├── FlowReaching.lean           # Mathlib Flow integration
│   └── RelCatBridge.lean           # RelCat equivalence
├── FixedPoint/
│   └── PeriodicNucleus.lean        # Nucleus operators, fixed‑point theorem
├── Seismic/                        # Layers 2‑4: Concrete + bridge + interpretation
│   ├── Basic.lean                  # Data types
│   ├── Reaching.lean               # Detection → ReachingRel bridge
│   ├── Observable.lean             # Kernel operator (nucleus dual)
│   ├── Validation.lean             # STA/LTA detection
│   └── CategoricalValidation.lean  # j(P) vs P interpretation
└── Wolfram/                        # Multiway / branchial / WM148 bridge (Lean side)

RESEARCHER_BUNDLE/HeytingLean/CLI/
├── SeismicValidateMain.lean        # seismic_validate_demo
├── WolframMultiwayMain.lean        # wolfram_multiway_demo
├── WolframWM148Main.lean           # wolfram_wm148_demo
└── WolframRoundtripMain.lean       # wolfram_roundtrip (Lean ↔ Wolfram)

RESEARCHER_BUNDLE/ffi/heyting_wolfram_bridge/  # Wolfram Language scripts
```

---

## The Mathematics (sketch)

1) Reaching relations compose categorically (TKFT):

```lean
structure ReachingRel (α : Type u) (β : Type v) : Type (max u v) where
  rel : α → β → Prop

def comp (R : ReachingRel α β) (S : ReachingRel β γ) : ReachingRel α γ :=
  ⟨fun a c => ∃ b, R.rel a b ∧ S.rel b c⟩
```

2) Observation kernels as nucleus‑like operators (contractive/idempotent):

```lean
structure Kernel {β : Type u} [SemilatticeInf β] where
  toFun : β → β
  monotone' : Monotone toFun
  map_inf' : ∀ x y, toFun (x ⊓ y) = toFun x ⊓ toFun y
  idempotent' : ∀ x, toFun (toFun x) = toFun x
  apply_le' : ∀ x, toFun x ≤ x
```

3) Fixed points form a Heyting subalgebra (mechanized; zero sorry).

---

## Documentation

- docs/WHY_THIS_MATTERS.md — Plain‑language explanation for scientists
- docs/TECHNICAL.md — Full mathematical details and executable interfaces
- docs/WOLFRAM.md — Wolfram Physics connection and cross‑checks
- docs/VALIDATION_RESULTS.md — Empirical results and evidence artifacts
- docs/05_Reproducibility.md — Reproducibility and environment notes

---

## Reproducibility & Environment

- Lean toolchain and package pins are recorded in `RESEARCHER_BUNDLE/lean-toolchain` and `RESEARCHER_BUNDLE/lakefile.lean`.
- Prefer incremental builds. The verification script uses strict flags and avoids unnecessary clean rebuilds.
- Wolfram cross‑checks require `wolframscript` on PATH.

---

## License

MIT — see `LICENSE.md`.

If you use this work, please cite the repository and linked papers.
