<img src="assets/Apoth3osis.webp" alt="Apoth3osis Logo" width="140"/>

<sub><strong>Our tech stack is ontological:</strong><br>
<strong>Hardware — Physics</strong><br>
<strong>Software — Mathematics</strong><br><br>
<strong>Our engineering workflow is simple:</strong> discover, build, grow, learn & teach</sub>

---

<sub>
<strong>Notice of Proprietary Information</strong><br>
This document outlines foundational concepts and methodologies developed during internal research and development at Apoth3osis. To protect our intellectual property and adhere to client confidentiality agreements, the code, architectural details, and performance metrics presented herein may be simplified, redacted, or presented for illustrative purposes only. This paper is intended to share our conceptual approach and does not represent the full complexity, scope, or performance of our production-level systems. The complete implementation and its derivatives remain proprietary.
</sub>

---

# Miranda Dynamics

**What physics, computation, and logic have in common — machine‑verified and empirically validated**

[![Lean 4](https://img.shields.io/badge/Lean-4-blue.svg)](https://lean-lang.org)
[![Mathlib](https://img.shields.io/badge/Mathlib-latest-purple.svg)](https://github.com/leanprover-community/mathlib4)
[![Sorry Count](https://img.shields.io/badge/sorry-0-brightgreen.svg)](RESEARCHER_BUNDLE/HeytingLean/MirandaDynamics/)
[![License: Apoth3osis License Stack v1](https://img.shields.io/badge/License-Apoth3osis%20License%20Stack%20v1-blue.svg)](LICENSE.md)
[![Live Demo](https://img.shields.io/badge/🌍_Live_Demo-View_Visualization-00ff88.svg)](https://abraxas1010.github.io/miranda-dynamics-lean/visualization/)

## Credo

> *"The book of nature is written in the language of mathematics."*
> — **Galileo Galilei**

This project demonstrates that the relationship between physical truth and observational knowledge has precise algebraic structure. Three independent research programs — Eva Miranda's dynamical systems, Stephen Wolfram's computational physics, and constructive logic — converged on the same mathematics. We formalize this convergence in Lean with machine-checked proofs.

### Acknowledgment

We humbly thank the collective intelligence of humanity for providing the technology and culture we cherish. We do our best to properly reference the authors of the works utilized herein, though we may occasionally fall short. Our formalization acts as a reciprocal validation—confirming the structural integrity of their original insights while securing the foundation upon which we build. In truth, all creative work is derivative; we stand on the shoulders of those who came before, and our contributions are simply the next link in an unbroken chain of human ingenuity.

---

## Proof Space Visualizations

<table>
<tr>
<td align="center" width="50%">
<strong>2D Proof Map</strong><br/>
<em>Click to explore: pan, zoom, search declarations</em><br/>
<a href="https://abraxas1010.github.io/miranda-dynamics-lean/RESEARCHER_BUNDLE/artifacts/visuals/miranda_2d.html">
  <img src="RESEARCHER_BUNDLE/artifacts/visuals/miranda_2d_preview.svg" alt="UMAP 2D preview" width="100%"/>
</a><br/>
<a href="https://abraxas1010.github.io/miranda-dynamics-lean/RESEARCHER_BUNDLE/artifacts/visuals/miranda_2d.html">▶ Open Interactive 2D Map</a>
</td>
<td align="center" width="50%">
<strong>3D Proof Map</strong><br/>
<em>Click to explore: rotate, zoom, click nodes</em><br/>
<a href="https://abraxas1010.github.io/miranda-dynamics-lean/RESEARCHER_BUNDLE/artifacts/visuals/miranda_3d.html">
  <img src="RESEARCHER_BUNDLE/artifacts/visuals/miranda_3d_preview_animated.svg" alt="UMAP 3D animated preview" width="100%"/>
</a><br/>
<a href="https://abraxas1010.github.io/miranda-dynamics-lean/RESEARCHER_BUNDLE/artifacts/visuals/miranda_3d.html">▶ Open Interactive 3D Map</a>
</td>
</tr>
<tr>
<td align="center" width="50%">
<strong>Tactic Flow Graph</strong><br/>
<em>Proof tactics and goal transformations</em><br/>
<a href="https://abraxas1010.github.io/miranda-dynamics-lean/RESEARCHER_BUNDLE/artifacts/visuals/tactic_flow.html">
  <img src="RESEARCHER_BUNDLE/artifacts/visuals/tactic_flow_preview.svg" alt="Tactic Flow preview" width="100%"/>
</a><br/>
<a href="https://abraxas1010.github.io/miranda-dynamics-lean/RESEARCHER_BUNDLE/artifacts/visuals/tactic_flow.html">▶ Open Interactive Tactic Flow</a>
</td>
<td align="center" width="50%">
<strong>Proof Term DAG</strong><br/>
<em>Abstract syntax tree of proof terms</em><br/>
<a href="https://abraxas1010.github.io/miranda-dynamics-lean/RESEARCHER_BUNDLE/artifacts/visuals/proof_term_dag.html">
  <img src="RESEARCHER_BUNDLE/artifacts/visuals/proof_term_dag_preview.svg" alt="Proof Term DAG preview" width="100%"/>
</a><br/>
<a href="https://abraxas1010.github.io/miranda-dynamics-lean/RESEARCHER_BUNDLE/artifacts/visuals/proof_term_dag.html">▶ Open Interactive Proof DAG</a>
</td>
</tr>
</table>

---

## The Discovery

Three research programs, working independently, discovered they were studying the same mathematical structure:

| Who | What They Study | Key Insight |
|-----|-----------------|-------------|
| Eva Miranda (Barcelona) | Billiards, fluid dynamics | "Any smooth dynamical system can compute anything." |
| Stephen Wolfram (Wolfram Physics) | Hypergraph rewriting | "Simple rules generate all of physics." |
| This Project | Formal logic in Lean | "Observation has algebraic structure." |

They all discovered the same thing: the relationship between what's true and what's observable follows precise algebraic laws.

---

## Documentation

| Document | Description |
|----------|-------------|
| **[Why This Matters](docs/WHY_THIS_MATTERS.md)** | Plain‑language explanation for scientists |
| **[Wolfram Connection](docs/WOLFRAM.md)** | Wolfram Physics bridge and cross‑checks |
| **[Technical Deep Dive](docs/TECHNICAL.md)** | Full mathematical details and executable interfaces |
| **[Validation Results](docs/VALIDATION_RESULTS.md)** | Empirical results and evidence artifacts |
| **[Reproducibility](docs/05_Reproducibility.md)** | Environment and build notes |

---

## Why This Matters

- **Physicists**: The gap between "particle arrives" and "detector fires" isn't noise — it's a fundamental logical structure that can be computed and predicted.
- **Computer scientists**: Turing completeness isn't just about silicon. Billiard balls, fluid flows, and seismic waves can all "compute" in the same formal sense.
- **Mathematicians**: Category theory provides the right language to unify these domains. We prove the link in Lean with zero unverified assumptions.
- **Data scientists**: Your 7% false‑negative rate might not be model error — it can be an irreducible epistemic uncertainty we can characterize precisely.

---

## Key Result (Real Data)

Validated against real seismic data:

| Metric | Value | Meaning |
|--------|-------|---------|
| Accuracy | 92.86% | Framework correctly predicts wave detection |
| Heyting Gap | 7.14% | True arrivals below detection threshold (j(P) < P) |
| False Positives | 0% | Never predicts detection without physics |

The "gap" isn't failure — it's the framework quantifying what's unknowable from finite observation.

**[→ See the Live Visualization](https://abraxas1010.github.io/miranda-dynamics-lean/visualization/)**

---

## Unified Framework (Miranda ⟷ Wolfram ⟷ Heyting)

| Framework | Core Object | "Reaching" | "Gap" |
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

## Reproducibility & Environment

- Lean toolchain and package pins are recorded in `RESEARCHER_BUNDLE/lean-toolchain` and `RESEARCHER_BUNDLE/lakefile.lean`.
- Prefer incremental builds. The verification script uses strict flags and avoids unnecessary clean rebuilds.
- Wolfram cross‑checks require `wolframscript` on PATH.

---

## License

[Apoth3osis License Stack v1](LICENSE.md) — see `licenses/` for full texts.

If you use this work, please cite the repository and linked papers.

---

<p align="center">
Part of the <a href="https://github.com/apoth3osis">HeytingLean</a> formalization project<br/>
<a href="https://apoth3osis.io">apoth3osis.io</a>
</p>
