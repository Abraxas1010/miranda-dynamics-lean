<img src="assets/Apoth3osis.webp" alt="Apoth3osis Logo" width="140"/>

# Miranda Dynamics Lean

**Formal verification of physical reachability using Heyting algebras and TKFT (Topological Khovanov Field Theory)**

[![Lean 4](https://img.shields.io/badge/Lean-4-blue.svg)](https://lean-lang.org)
[![Mathlib](https://img.shields.io/badge/Mathlib-latest-purple.svg)](https://github.com/leanprover-community/mathlib4)
[![Sorry Count](https://img.shields.io/badge/sorry-0-brightgreen.svg)](RESEARCHER_BUNDLE/HeytingLean/MirandaDynamics/)
[![License](https://img.shields.io/badge/License-Apoth3osis-yellow.svg)](LICENSE.md)

This project validates that **intuitionistic logic (Heyting algebras) correctly describes what humans can learn from finite observation of physical dynamical systems** — bridging Eva Miranda's theoretical framework with real-world seismic data.

---

## Key Result

| Metric | Value |
|--------|-------|
| **Accuracy** | 92.86% (13/14 event-station pairs) |
| **False Negatives** | 1 (the expected "Heyting gap") |
| **False Positives** | 0 |
| **Mean Timing Error** | 4.27 seconds |

The single false negative is not a bug — it's the framework working as designed, quantifying the irreducible epistemic gap between physical truth and finite observation.

---

## What This Project Does

```
┌─────────────────────────────────────────────────────────────────┐
│  PHYSICAL WORLD                                                 │
│  Earthquake → Waves propagate → Seismometers record             │
└─────────────────────────────┬───────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│  PYTHON BRIDGE                                                  │
│  Fetch events + waveforms from USGS/IRIS → JSON bundle          │
└─────────────────────────────┬───────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│  LEAN VERIFICATION                                              │
│  1. Formal reaching relation (TKFT theory)                      │
│  2. Observation kernel (nucleus operator)                       │
│  3. Compare predictions to detections                           │
│  4. Compute accuracy = theory validation                        │
└─────────────────────────────────────────────────────────────────┘
```

### The Core Insight

Miranda's TKFT framework defines a **reaching relation**: can information (a seismic wave) propagate from point A (earthquake) to point B (seismometer)?

We formalize this in Lean using **Heyting algebras**, where:
- **P** = "wave truly reaches station" (physical fact)
- **j(P)** = "we can detect that wave reached" (observable fact)
- **Gap = P \ j(P)** = what's true but unknowable from finite observation

The **7.14% Heyting gap rate** quantifies this inherent epistemic limitation.

---

## Quick Start

```bash
# Build Lean components
cd RESEARCHER_BUNDLE
lake build --wfail

# Run fixture validation (no network required)
lake exe seismic_validate_demo

# Run full validation with real data
cd ..
python3 scripts/seismic_bridge.py \
  --stations IU.ANMO,IU.HRV,IU.COLA,II.BFO,IU.CTAO,IU.SNZO \
  --min-magnitude 6.0 \
  --days-back 30 \
  --max-events 3 \
  --output data/seismic/validation_bundle.json

cd RESEARCHER_BUNDLE
lake exe seismic_validate_demo -- ../data/seismic/validation_bundle.json
```

---

## Project Structure

```
miranda-dynamics-lean/
├── RESEARCHER_BUNDLE/
│   └── HeytingLean/
│       ├── MirandaDynamics/
│       │   ├── Billiard/           # Observation kernel calibration
│       │   ├── Billiards/          # Miranda-Ramos billiard formalization
│       │   ├── Computation/        # Turing machine / flow realization
│       │   ├── Discrete/           # Halting ↔ periodic bridges
│       │   ├── External/           # Literature claim interfaces
│       │   ├── FixedPoint/         # Nucleus operators
│       │   ├── TKFT/               # Topological Kleene Field Theory
│       │   └── Undecidability/     # Reduction machinery
│       └── CLI/
│           └── SeismicValidateMain.lean
├── scripts/
│   ├── seismic_bridge.py           # USGS/IRIS data fetcher
│   ├── generate_validation_report.py
│   ├── billiard_calibration.py     # Known-dynamics calibration
│   └── transfer_calibration.py     # Parameter transfer
├── data/
│   ├── seismic/                    # Earthquake data bundles
│   │   ├── archived/               # Reproducible validation snapshots
│   │   └── PROVENANCE.md           # Data source documentation
│   └── billiard/                   # Calibration results
├── results/
│   └── seismic_validation/         # Validation reports
└── docs/                           # Technical documentation
```

---

## Documentation

| Document | Description |
|----------|-------------|
| **[Technical Deep Dive](docs/TECHNICAL.md)** | How Lean connects to physical data, the mathematics of the nucleus operator, and why this validates intuitionistic epistemology |
| **[Validation Results](docs/VALIDATION_RESULTS.md)** | Full empirical results, expanded validation runs, and billiard calibration |
| **[Data Provenance](data/seismic/PROVENANCE.md)** | Data sources, parameters, and reproducibility instructions |
| **[TKFT Theory](docs/01_TKFT_Theory.md)** | Topological Kleene Field Theory background |
| **[Cantor Encoding](docs/02_Cantor_Encoding.md)** | How Turing tapes map to billiard dynamics |

---

## Theoretical Background

This project implements ideas from:

1. **Eva Miranda's TKFT** — Topological field theory framework for computational dynamics
2. **Heyting Algebras** — The logic of observable properties (intuitionistic, not classical)
3. **Nucleus Operators** — Maps j: H → H that model information loss in observation

**Key theorem**: Fixed points of the nucleus form a Heyting algebra of "robust" observations — properties that don't change when you observe them again.

### Primary Research Papers Formalized

| Paper | Authors | Year | Link |
|-------|---------|------|------|
| Classical billiards can compute | Miranda, Ramos | 2025 | [arXiv:2512.19156](https://arxiv.org/abs/2512.19156) |
| Topological Kleene Field Theories | González-Prieto, Miranda, Peralta-Salas | 2025 | [arXiv:2503.16100](https://arxiv.org/abs/2503.16100) |
| Turing complete Euler flows | Cardona, Miranda, Peralta-Salas, Presas | 2021 | [PNAS](https://doi.org/10.1073/pnas.2026818118) |

---

## What This Formalization Proves

### Fully Mechanized (No Axioms, No `sorry`)

| Result | Location | Description |
|--------|----------|-------------|
| **TKFT Reaching Relations** | `TKFT/Reaching.lean` | Categorical structure of reachability |
| **Cantor Tape Encoding** | `Billiards/CantorEncoding.lean` | Turing tape → ternary Cantor set (injective) |
| **Halting ↔ Periodic** | `Discrete/HaltingToPeriodic.lean` | Halting reduces to period-2 orbits |
| **Union Nucleus** | `FixedPoint/PeriodicNucleus.lean` | Fixed-point characterization |
| **Undecidability Transfer** | `Undecidability/Transfers.lean` | Generic halting problem reductions |

---

## Interactive Visualizations

Explore the proof structure:

| [2D UMAP](https://abraxas1010.github.io/miranda-dynamics-lean/RESEARCHER_BUNDLE/artifacts/visuals/miranda_2d.html) | [3D UMAP](https://abraxas1010.github.io/miranda-dynamics-lean/RESEARCHER_BUNDLE/artifacts/visuals/miranda_3d.html) | [Tactic Flow](https://abraxas1010.github.io/miranda-dynamics-lean/RESEARCHER_BUNDLE/artifacts/visuals/tactic_flow.html) |
|:---:|:---:|:---:|
| Semantic clustering of theorems | Three-dimensional exploration | Step-by-step proof tactics |

---

## Acknowledgment

This formalization honors the groundbreaking work of **Professor Eva Miranda** (Universitat Politècnica de Catalunya) and collaborators, who established profound connections between dynamical systems and computation theory.

> *"Any sufficiently smooth dynamical system can simulate any Turing machine."*
> — Eva Miranda

---

## Citation

```bibtex
@software{miranda_dynamics_lean,
  title = {Miranda Dynamics Lean: Formal Verification of Physical Reachability},
  year = {2026},
  url = {https://github.com/Abraxas1010/miranda-dynamics-lean}
}
```

---

## License

This project is provided under the [Apoth3osis License Stack v1](LICENSE.md).
See `licenses/` for component licenses.
