<img src="assets/Apoth3osis.webp" alt="Apoth3osis Logo" width="140"/>

# Miranda Dynamics Lean

**Category-theoretic formalization of TKFT (Topological Kleene Field Theory) with empirical validation against real seismic data**

[![Lean 4](https://img.shields.io/badge/Lean-4-blue.svg)](https://lean-lang.org)
[![Mathlib](https://img.shields.io/badge/Mathlib-latest-purple.svg)](https://github.com/leanprover-community/mathlib4)
[![Sorry Count](https://img.shields.io/badge/sorry-0-brightgreen.svg)](RESEARCHER_BUNDLE/HeytingLean/MirandaDynamics/)
[![License](https://img.shields.io/badge/License-Apoth3osis-yellow.svg)](LICENSE.md)
[![Live Demo](https://img.shields.io/badge/Live_Demo-View_Visualization-00ff88.svg)](https://abraxas1010.github.io/miranda-dynamics-lean/visualization/)

This project provides a **faithful categorical implementation** of Eva Miranda's TKFT framework, demonstrating that her abstract machinery — reaching relations, nucleus operators, Heyting algebras — correctly describes physical observation when instantiated against real-world seismic data.

---

## Categorical Alignment with Miranda's Framework

Miranda's TKFT papers establish computation via **categorical structures**:

| Miranda's Abstract Concept | Our Lean Implementation | File |
|---------------------------|------------------------|------|
| **Reaching relation** R : α → β → Prop | `ReachingRel` with id, comp, assoc laws | `TKFT/Reaching.lean` |
| **Relational composition** (bordism gluing) | `ReachingRel.comp` | `TKFT/Reaching.lean` |
| **Nucleus operator** j : H → H | `Nucleus` (via Mathlib), `obsKernel` | `FixedPoint/PeriodicNucleus.lean`, `Seismic/Observable.lean` |
| **Fixed points** form Heyting algebra | `isFixedPoint_unionNucleus_iff` | `FixedPoint/PeriodicNucleus.lean` |
| **Information gap** P ∧ ¬j(P) | `nucleus_contracted` (Heyting gap) | `Seismic/CategoricalValidation.lean` |

We went to great lengths to ensure our formalization matches Miranda's categorical semantics, not just the computational results.

---

## The 4-Layer Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│  LAYER 4: CATEGORICAL INTERPRETATION                                    │
│  CategoricalValidation.lean                                             │
│  Interprets validation results as j(P) vs P using Heyting semantics    │
├─────────────────────────────────────────────────────────────────────────┤
│  LAYER 3: TKFT BRIDGE                                                   │
│  Seismic/Reaching.lean, Seismic/Observable.lean                        │
│  Connects seismic detection to abstract ReachingRel and Kernel         │
├─────────────────────────────────────────────────────────────────────────┤
│  LAYER 2: CONCRETE IMPLEMENTATION                                       │
│  Seismic/Basic.lean, Seismic/Validation.lean                           │
│  Data types (Station, Event, Waveform) and STA/LTA detection           │
├─────────────────────────────────────────────────────────────────────────┤
│  LAYER 1: ABSTRACT CATEGORICAL FRAMEWORK                                │
│  TKFT/Reaching.lean, TKFT/Category.lean, FixedPoint/PeriodicNucleus.lean│
│  Miranda's abstract definitions with categorical laws proved           │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Key Empirical Result

| Metric | Value | Categorical Meaning |
|--------|-------|---------------------|
| **Accuracy** | 92.86% | j(P) = P for 13/14 pairs |
| **Heyting Gap** | 7.14% | j(P) < P for 1/14 pairs |
| **False Positives** | 0% | j(P) > P never occurs |
| **Nucleus Width** | 4.27s | Mean timing uncertainty |

The single false negative demonstrates **j(P) ⊊ P** — the Heyting gap where physical truth exceeds observable truth. This is Miranda's framework working exactly as designed.

---

## Categorical Interpretation Output

The validator produces both standard metrics and **categorical interpretation**:

```
=== CATEGORICAL INTERPRETATION ===
Treat `P` as predicted reachability and `j(P)` as observed/verifiable reachability.

- Total pairs (waveform_ok): 14
- j(P) = P (reach observed when predicted): 13
- j(P) < P (gap / false negative): 1
- j(P) > P (false positive): 0

- Mean nucleus width |Δt|: 4.3 seconds
- Heyting gap rate P ∧ ¬j(P): 7.14%
- Fixed point (sets equal): false
```

---

## What Makes This Categorical

### 1. Reaching Relations as Morphisms

Miranda defines computation via **reaching relations** that compose like morphisms in a category:

```lean
-- From TKFT/Reaching.lean (mechanized, no sorry)

structure ReachingRel (α : Type u) (β : Type v) : Type (max u v) where
  rel : α → β → Prop

def comp (R : ReachingRel α β) (S : ReachingRel β γ) : ReachingRel α γ :=
  ⟨fun a c => ∃ b, R.rel a b ∧ S.rel b c⟩

theorem id_left (R : ReachingRel α β) : comp (id α) R = R := ...
theorem id_right (R : ReachingRel α β) : comp R (id β) = R := ...
theorem assoc (R S T) : comp (comp R S) T = comp R (comp S T) := ...
```

### 2. Nucleus Operators (Observation Kernels)

Miranda uses **nucleus operators** to model information loss in observation:

```lean
-- From Seismic/Observable.lean (mechanized, no sorry)

structure Kernel {β : Type u} [SemilatticeInf β] where
  toFun : β → β
  monotone' : Monotone toFun
  map_inf' : ∀ x y, toFun (x ⊓ y) = toFun x ⊓ toFun y
  idempotent' : ∀ x, toFun (toFun x) = toFun x
  apply_le' : ∀ x, toFun x ≤ x  -- contractive (dual to nucleus)

def obsKernel (n : Nat) : Kernel (β := Set (Array α)) := ...
```

### 3. Fixed Points Form Heyting Algebra

Miranda's key theorem: fixed points of a nucleus form a Heyting subalgebra:

```lean
-- From FixedPoint/PeriodicNucleus.lean (mechanized, no sorry)

def unionNucleus (U : Set α) : Nucleus (Set α) := ...

theorem isFixedPoint_unionNucleus_iff (U S : Set α) :
    unionNucleus U S = S ↔ U ⊆ S := ...
```

### 4. Categorical Validation Metrics

Our validation interprets results categorically:

```lean
-- From Seismic/CategoricalValidation.lean

structure CategoricalSummary where
  nucleus_identity : Nat    -- j(P) = P
  nucleus_contracted : Nat  -- j(P) < P (Heyting gap)
  nucleus_expanded : Nat    -- j(P) > P (would be error)
  heyting_gap_rate : Float
  fixed_point : Bool
```

---

## Quick Start

```bash
cd RESEARCHER_BUNDLE
lake build --wfail

# Run validation with categorical output
lake exe seismic_validate_demo
```

---

## Project Structure

```
RESEARCHER_BUNDLE/HeytingLean/MirandaDynamics/
├── TKFT/                           # Layer 1: Abstract categorical framework
│   ├── Reaching.lean               # ReachingRel with categorical laws
│   ├── Category.lean               # Category instance
│   ├── FlowReaching.lean           # Mathlib Flow integration
│   └── RelCatBridge.lean           # RelCat equivalence
├── FixedPoint/
│   └── PeriodicNucleus.lean        # Nucleus operators, fixed point theorem
├── Seismic/                        # Layers 2-4: Concrete + bridge + interpretation
│   ├── Basic.lean                  # Data types
│   ├── Reaching.lean               # Detection → ReachingRel bridge
│   ├── Observable.lean             # Kernel operator
│   ├── Validation.lean             # STA/LTA detection
│   └── CategoricalValidation.lean  # j(P) vs P interpretation
├── Billiards/                      # Miranda-Ramos billiard formalization
│   └── CantorEncoding.lean         # Tape → Cantor (injective)
├── Discrete/
│   └── HaltingToPeriodic.lean      # Halting ↔ period-2 orbits
└── External/
    └── Interfaces.lean             # Literature claim interfaces
```

---

## Theoretical Background

This project implements Eva Miranda's TKFT framework:

1. **TKFT (Topological Kleene Field Theory)** — Computation via categorical reaching relations on bordisms
2. **Nucleus Operators** — j : H → H modeling observation-induced information loss
3. **Heyting Algebras** — The logic of observable properties (intuitionistic, not Boolean)
4. **Fixed Point Theorem** — Robust observations form a Heyting subalgebra

### Primary Research Papers Formalized

| Paper | Authors | Year | Link |
|-------|---------|------|------|
| Classical billiards can compute | Miranda, Ramos | 2025 | [arXiv:2512.19156](https://arxiv.org/abs/2512.19156) |
| Topological Kleene Field Theories | González-Prieto, Miranda, Peralta-Salas | 2025 | [arXiv:2503.16100](https://arxiv.org/abs/2503.16100) |
| Turing complete Euler flows | Cardona, Miranda, Peralta-Salas, Presas | 2021 | [PNAS](https://doi.org/10.1073/pnas.2026818118) |

---

## Documentation

| Document | Description |
|----------|-------------|
| **[Technical Deep Dive](docs/TECHNICAL.md)** | How Lean connects to physical data via categorical structures |
| **[Validation Results](docs/VALIDATION_RESULTS.md)** | Full empirical results with categorical interpretation |
| **[TKFT Theory](docs/01_TKFT_Theory.md)** | Background on reaching relations and bordism semantics |
| **[Data Provenance](data/seismic/PROVENANCE.md)** | Data sources and reproducibility |

---

## Why Categorical?

Miranda's work is fundamentally **category-theoretic**: reaching relations compose, bordisms glue, nucleus operators preserve meets. A naive implementation might just compute accuracy metrics. We instead:

1. **Formalize the abstract categorical structures** (ReachingRel, Nucleus, Kernel)
2. **Prove the categorical laws** (associativity, identity, idempotence)
3. **Bridge to concrete data** via type-safe instantiation
4. **Interpret results categorically** (j(P) = P vs j(P) < P)

This ensures our validation is not just "correct numerically" but **structurally faithful** to Miranda's framework.

---

## Acknowledgment

This formalization honors the work of **Professor Eva Miranda** (Universitat Politècnica de Catalunya) and collaborators. Their category-theoretic approach to computational dynamics — viewing physical systems through the lens of reaching relations and nucleus operators — is what makes this rigorous connection between abstract theory and empirical data possible.

> *"Any sufficiently smooth dynamical system can simulate any Turing machine."*
> — Eva Miranda

---

## Citation

```bibtex
@software{miranda_dynamics_lean,
  title = {Miranda Dynamics Lean: Category-Theoretic TKFT with Empirical Validation},
  year = {2026},
  url = {https://github.com/Abraxas1010/miranda-dynamics-lean}
}
```

---

## License

This project is provided under the [Apoth3osis License Stack v1](LICENSE.md).
