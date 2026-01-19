// Miranda Dynamics Proof Term DAG Data
// Abstract syntax trees of key proof terms

const proofTermData = {
  theorems: [
    {
      name: "encodeTape_injective",
      file: "Billiards/CantorEncoding.lean",
      description: "Injectivity of Cantor tape encoding",
      statement: "Function.Injective encodeTape",
      nodes: [
        { id: "root", type: "app", label: "Function.Injective.intro", depth: 0 },
        { id: "lam1", type: "lam", label: "λ t₁ t₂ h =>", depth: 1 },
        { id: "app1", type: "app", label: "funext", depth: 2 },
        { id: "lam2", type: "lam", label: "λ k =>", depth: 3 },
        { id: "app2", type: "app", label: "digit_eq_of_encode_eq", depth: 4 },
        { id: "var1", type: "var", label: "h", depth: 5 },
        { id: "var2", type: "var", label: "k", depth: 5 }
      ],
      edges: [
        { from: "root", to: "lam1" },
        { from: "lam1", to: "app1" },
        { from: "app1", to: "lam2" },
        { from: "lam2", to: "app2" },
        { from: "app2", to: "var1" },
        { from: "app2", to: "var2" }
      ]
    },
    {
      name: "ReachingRel.assoc",
      file: "TKFT/Reaching.lean",
      description: "Associativity of reaching relation composition",
      statement: "(r ∘ᵣ s) ∘ᵣ t = r ∘ᵣ (s ∘ᵣ t)",
      nodes: [
        { id: "root", type: "app", label: "ReachingRel.ext", depth: 0 },
        { id: "lam1", type: "lam", label: "λ x z =>", depth: 1 },
        { id: "app1", type: "app", label: "Iff.intro", depth: 2 },
        { id: "lam2", type: "lam", label: "λ ⟨y, ⟨w, hrw, hwy⟩, hyz⟩ =>", depth: 3 },
        { id: "mk1", type: "mk", label: "⟨w, hrw, y, hwy, hyz⟩", depth: 4 },
        { id: "lam3", type: "lam", label: "λ ⟨w, hrw, y, hwy, hyz⟩ =>", depth: 3 },
        { id: "mk2", type: "mk", label: "⟨y, ⟨w, hrw, hwy⟩, hyz⟩", depth: 4 }
      ],
      edges: [
        { from: "root", to: "lam1" },
        { from: "lam1", to: "app1" },
        { from: "app1", to: "lam2" },
        { from: "app1", to: "lam3" },
        { from: "lam2", to: "mk1" },
        { from: "lam3", to: "mk2" }
      ]
    },
    {
      name: "isFixedPoint_unionNucleus_iff",
      file: "FixedPoint/PeriodicNucleus.lean",
      description: "Fixed point characterization",
      statement: "IsFixedPoint (unionNucleus U) S ↔ U ⊆ S",
      nodes: [
        { id: "root", type: "app", label: "Iff.intro", depth: 0 },
        { id: "lam1", type: "lam", label: "λ h =>", depth: 1 },
        { id: "calc1", type: "calc", label: "calc U ⊆ S ∪ U = S", depth: 2 },
        { id: "app1", type: "app", label: "h ▸ subset_union_right", depth: 3 },
        { id: "lam2", type: "lam", label: "λ h =>", depth: 1 },
        { id: "app2", type: "app", label: "union_eq_self_of_subset_right", depth: 2 },
        { id: "var1", type: "var", label: "h", depth: 3 }
      ],
      edges: [
        { from: "root", to: "lam1" },
        { from: "root", to: "lam2" },
        { from: "lam1", to: "calc1" },
        { from: "calc1", to: "app1" },
        { from: "lam2", to: "app2" },
        { from: "app2", to: "var1" }
      ]
    },
    {
      name: "reachesPeriod2_iff_halts",
      file: "Discrete/HaltingToPeriodic.lean",
      description: "Halting ↔ periodic equivalence",
      statement: "reachesPeriod2 ↔ halts",
      nodes: [
        { id: "root", type: "app", label: "Iff.intro", depth: 0 },
        { id: "lam1", type: "lam", label: "λ ⟨n, hper⟩ =>", depth: 1 },
        { id: "app1", type: "app", label: "halts_of_periodic", depth: 2 },
        { id: "var1", type: "var", label: "hper", depth: 3 },
        { id: "lam2", type: "lam", label: "λ ⟨n, hhalt⟩ =>", depth: 1 },
        { id: "mk1", type: "mk", label: "⟨n, periodic_of_halt hhalt⟩", depth: 2 }
      ],
      edges: [
        { from: "root", to: "lam1" },
        { from: "root", to: "lam2" },
        { from: "lam1", to: "app1" },
        { from: "app1", to: "var1" },
        { from: "lam2", to: "mk1" }
      ]
    },
    {
      name: "not_computable_of_reduces",
      file: "Undecidability/Transfers.lean",
      description: "Undecidability transfer",
      statement: "¬Computable Q → Reduces P Q → ¬Computable P",
      nodes: [
        { id: "root", type: "lam", label: "λ hQ hred hP =>", depth: 0 },
        { id: "app1", type: "app", label: "hQ", depth: 1 },
        { id: "app2", type: "app", label: "computable_of_reduces", depth: 2 },
        { id: "var1", type: "var", label: "hred", depth: 3 },
        { id: "var2", type: "var", label: "hP", depth: 3 }
      ],
      edges: [
        { from: "root", to: "app1" },
        { from: "app1", to: "app2" },
        { from: "app2", to: "var1" },
        { from: "app2", to: "var2" }
      ]
    }
  ]
};

if (typeof module !== 'undefined') {
  module.exports = proofTermData;
}
