# Philosophical Foundations: Haptic Realism and Constructive Mathematics

> *"The wrong way to think about human perception is to take it as aiming to reveal to us how things are in themselves, instead of in terms of their human-relative properties. The same goes for science."*  
> — Mazviita Chirimuuta, *Haptic Realism for Neuroscience* (2023)

> *"Any sufficiently smooth dynamical system can simulate any Turing machine."*  
> — Eva Miranda, on computational universality in contact flows (2025)

---

## Overview

This document articulates the philosophical foundations underlying the HeytingLean formalization of Miranda dynamics. We show that our formal framework provides machine-verified foundations for **haptic realism** — Mazviita Chirimuuta's thesis that scientific knowledge is constructed through interaction rather than passive observation.

The convergence is not accidental. Both Chirimuuta's philosophy of science and our constructive mathematics address the same fundamental question: *How can there be objective knowledge when all knowledge is observer-relative?*

---

## The HeytingLean Ontology

Our framework rests on three foundational claims:

### Claim 1: Generative Mathematics as Ontology

The universe is constituted by generative mathematical structures — not static objects obeying external laws, but dynamic processes that produce structure through iteration. Miranda's TKFT (Topological Kleene Field Theory) formalizes this: computation proceeds through bordisms connecting input to output manifolds, with the reaching relation defining what can be constructed from what.

```
Universe = Generative Process, not Static Collection
```

### Claim 2: The Provable and the Unprovable

Our formalization captures both what CAN be reached/proven AND what CANNOT. The **Heyting gap** — the strict inequality `j P < P` where `j` is a nucleus operator — represents structure that exists but is not accessible from a given observer's position.

```lean
theorem heyting_gap_is_nonreaching : 
    j P < P ↔ ∃ input, ¬TKFT.reaches input (TKFT.output P)
```

This is not a limitation to be overcome but a fundamental feature of constructive knowledge.

### Claim 3: Observer-Relative Verification

The ability to predict and verify outcomes is relative to and dependent on the observer. Different observers (modeled as different nucleus operators) have access to different subsets of mathematical reality. There is no "view from nowhere" — every perspective is a perspective *from somewhere*.

```
Knowledge = Fixed points of observer's nucleus
         = What that observer can computationally reach
```

---

## Chirimuuta's Haptic Realism

Mazviita Chirimuuta (University of Edinburgh, 2025 Lakatos Award winner) develops **haptic realism** as an alternative to both naive scientific realism and social constructivism. Her key insight: the metaphor of *touch* better captures scientific knowledge than the metaphor of *vision*.

### Vision vs. Touch as Epistemic Metaphors

| Visual Metaphor | Haptic Metaphor |
|-----------------|-----------------|
| Passive reception | Active exploration |
| Distance from object | Contact with object |
| Reveals things "as they are" | Reveals things "as they interact with us" |
| Single correct picture | Multiple valid probings |
| Knowledge despite interaction | Knowledge *in virtue of* interaction |

Traditional scientific realism assumes a "God's eye view" — that science progressively reveals objective reality independent of our methods. Chirimuuta argues this is incoherent. Just as touch requires contact and purposeful exploration, scientific knowledge requires manipulation, simplification, and interaction with phenomena.

### Three Elements of Perspectivism

Chirimuuta identifies three features that characterize perspectival knowledge:

1. **Partiality** — Perspectives reveal only partial aspects of their targets
2. **Interestedness** — Knowledge is shaped by the investigator's goals and purposes
3. **Interaction** — Knowledge emerges through manipulation, not passive observation

### Formal Idealism

A crucial consequence: we cannot infer ontological commitment from successful modeling. The patterns scientists discover are reproducible, but they are not "natural furniture of the world" — they are co-constructed by the interaction between investigator and investigated.

---

## The Mapping: HeytingLean ↔ Haptic Realism

The correspondence between our formal framework and Chirimuuta's philosophy is precise:

| HeytingLean Concept | Haptic Realism Concept | Explanation |
|---------------------|------------------------|-------------|
| Nucleus operator `j` | Observer's perspective / simplification strategy | The nucleus determines what an observer can access |
| Fixed points `{x : j(x) = x}` | Observable/tangible knowledge | What survives the observer's simplification |
| Heyting gap `j P < P` | Formal idealism | Structure lost in observation — cannot infer ontology from models |
| `ReachingRel` morphisms | Purposeful exploration | Computational paths = active probing |
| Multiple nuclei on same Frame | Perspectival pluralism | Different observers, non-converging descriptions |
| Frame (complete Heyting algebra) | Underlying reality | Objective structure that all perspectives probe |

### The Nucleus IS the Haptic Interface

The nucleus operator `j : Frame → Frame` formalizes exactly what Chirimuuta describes:

- **Partiality**: `j P ≤ P` — the nucleus can only access part of what exists
- **Interestedness**: Different nuclei represent different "interests" or simplification strategies  
- **Interaction**: The reaching relation defines knowledge through dynamical contact

The Heyting gap `j P < P` (strict inequality) is **formal idealism made precise**: there exist propositions `P` such that `P` holds but `j P` does not — the observer's perspective cannot capture the full structure.

### Constructive Logic as the Logic of Interaction

Why Heyting algebras rather than Boolean algebras? Because:

- **Boolean logic** assumes excluded middle: every proposition is either true or false, independent of our ability to determine which
- **Heyting logic** is constructive: truth requires a construction, a proof, a *reaching*

This is the logic appropriate for haptic realism. You cannot passively observe that `P ∨ ¬P` — you must actively construct a proof of one or the other. Knowledge requires computational work.

---

## Miranda's Physics as Haptic Epistemology

Eva Miranda's results on computational universality provide the *physical demonstration* of haptic realism.

### The Billiard Ball Touches the Boundary

Miranda-Ramos (2025) prove that billiard dynamics can simulate any Turing machine. This is literally haptic:

- The ball makes **contact** with polygon boundaries
- It **explores** configuration space through collisions
- Computation emerges **in virtue of** these physical interactions

The billiard ball "knows" the result of a computation by touching walls — not by passive observation, but by active, physical engagement with its environment.

### Computational Irreducibility = No Shortcut

Wolfram's principle of computational irreducibility aligns perfectly:

> "The only way to determine the outcome of a computationally irreducible process is to run it step by step — there are no shortcuts."

This is Chirimuuta's claim that there is no "framework-independent" way of generating knowledge. You cannot skip the interaction. The dynamics must unfold; the ball must bounce; the observer must probe.

### Multiple Realizations as Perspectival Pluralism

Miranda shows the SAME Turing computation can be realized as:

- Billiard trajectories (Miranda-Ramos 2025)
- Euler fluid flows (Cardona-Miranda-Peralta-Presas 2021)
- Navier-Stokes steady states (Dyhr et al. 2025)
- Contact Reeb flows (Cardona et al. 2019)

These are Chirimuuta's "unrecognizably different descriptions" — distinct physical systems encoding identical computational content. Each is a valid perspective; none is privileged; they do not converge to a single "correct" description.

Our framework captures this: different physical embeddings correspond to different nuclei on the same underlying Frame, producing different but equally valid Heyting subalgebras of accessible knowledge.

---

## The Unified Picture

### Classical vs. Constructive Epistemology

| Classical (Boolean) View | Constructive (Heyting) View |
|--------------------------|----------------------------|
| Passive observation reveals truth | Active construction produces knowledge |
| Single objective reality | Multiple valid perspectives |
| Knowledge independent of knower | Knowledge relative to observer's nucleus |
| Excluded middle: `P ∨ ¬P` always | Excluded middle fails: some `P` undecidable |
| Physics = laws on inert matter | Physics = computation through interaction |

### The Ontological Stack

```
CHIRIMUUTA — Philosophy of Science
"Haptic realism: knowledge through interaction, not passive mirroring"
                    ↓
MIRANDA — Mathematical Physics  
"Physical dynamics = universal computation; no shortcut to halting"
                    ↓
HEYTINGLEAN — Formal Verification
"Nucleus j captures observer perspective; gap j P < P is formal idealism"
                    ↓
CONSTRUCTIVE MATHEMATICS — Logical Foundation
"Truth requires construction; Heyting algebras encode observer-relative provability"
```

Each layer validates the others:
- Miranda gives Chirimuuta a physics substrate
- Chirimuuta gives Miranda an epistemology
- HeytingLean provides machine-checked rigor
- Constructive logic explains why they converge

---

## Implications

### For Philosophy of Science

Haptic realism now has formal foundations. The intuitive claim that "knowledge is constructed through interaction" can be made precise: knowledge consists of the fixed points of an observer's nucleus operator, and the Heyting gap quantifies what is necessarily lost in any perspective.

### For Foundations of Mathematics

The choice between classical and constructive mathematics is not merely technical — it reflects a fundamental epistemological commitment. Classical mathematics assumes a God's eye view; constructive mathematics accepts observer-relativity as basic.

### For Physics

Miranda's results suggest that computational universality is generic in physics. If so, then physical systems are not "objects obeying laws" but "perspectives computing their own evolution." The billiard table is not a passive arena but an active participant in constructing its own behavior.

### For This Formalization

The theorems in HeytingLean/MirandaDynamics are not merely mathematical curiosities — they provide verified foundations for a post-Newtonian epistemology in which:

- Objectivity is preserved (the Frame exists independently of observers)
- Relativity is acknowledged (each nucleus accesses different fixed points)
- Constructivity is required (knowledge demands computational work)
- Pluralism is embraced (multiple non-converging perspectives are valid)

---

## References

### Primary Sources

**Chirimuuta, M.** (2016). Vision, perspectivism, and haptic realism. *Philosophy of Science*, 83(5), 746-756.

**Chirimuuta, M.** (2023). Haptic realism for neuroscience. *Synthese*, 202(3), 1-16.

**Chirimuuta, M.** (2024). *The Brain Abstracted: Simplification in the History and Philosophy of Neuroscience*. MIT Press. [2025 Lakatos Award Winner]

**Miranda, E., & Ramos, I.** (2025). Classical billiards can compute. arXiv:2512.19156

**González-Prieto, Á., Miranda, E., & Peralta-Salas, D.** (2025). Topological Kleene Field Theories as a model of computation. arXiv:2503.16100

### Background

**Johnstone, P.T.** (1982). *Stone Spaces*. Cambridge University Press. [Frame theory, nucleus operators]

**Martin-Löf, P.** (1984). *Intuitionistic Type Theory*. Bibliopolis. [Constructive foundations]

**Wolfram, S.** (2020). *A Project to Find the Fundamental Theory of Physics*. Wolfram Media. [Computational irreducibility]

---

## Appendix: Key Theorems Referenced

The following theorems from HeytingLean/MirandaDynamics formalize the concepts discussed:

```lean
-- The Heyting gap captures formal idealism
theorem heyting_gap_is_nonreaching : 
    j P < P ↔ ∃ input, ¬TKFT.reaches input (TKFT.output P)

-- Halting ↔ Periodic: computation reduces to dynamics
theorem reachesPeriod2_iff_halts (n : Nat) (c : Nat.Partrec.Code) :
    ReachesPeriod2 n c ↔ Undecidability.Halting.Halts n c

-- Undecidability transfers across perspectives
theorem not_computable_of_reduces {P Q : ℕ → Prop}
    (hQ : ¬Computable Q) (hred : Reduces P Q) : ¬Computable P

-- Tape encoding preserves structure through interaction
theorem encodeTape_injective : Function.Injective encodeTape
```

These are not new proofs required — they already exist in the repository. This document explains what they *mean* philosophically.

---

*Part of the HeytingLean formalization project • [apoth3osis.io](https://apoth3osis.io)*
