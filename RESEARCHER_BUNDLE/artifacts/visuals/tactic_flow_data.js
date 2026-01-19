// Miranda Dynamics Tactic Flow Data
// Key theorems with proof tactic traces

const tacticFlowData = {
  theorems: [
    {
      name: "encodeTape_injective",
      file: "Billiards/CantorEncoding.lean",
      description: "Cantor tape encoding is injective",
      statement: "Function.Injective encodeTape",
      nodes: [
        { id: "goal_0", type: "goal", label: "⊢ Function.Injective encodeTape", depth: 0 },
        { id: "tactic_1", type: "tactic", label: "intro t₁ t₂ h", depth: 1 },
        { id: "hyp_2", type: "hypothesis", label: "h : encodeTape t₁ = encodeTape t₂", depth: 1 },
        { id: "goal_3", type: "goal", label: "⊢ t₁ = t₂", depth: 2 },
        { id: "tactic_4", type: "tactic", label: "ext k", depth: 2 },
        { id: "goal_5", type: "goal", label: "⊢ t₁ k = t₂ k", depth: 3 },
        { id: "tactic_6", type: "tactic", label: "apply digit_eq_of_encode_eq", depth: 3 },
        { id: "tactic_7", type: "tactic", label: "exact h", depth: 4 },
        { id: "qed_8", type: "qed", label: "QED", depth: 5 }
      ],
      edges: [
        { from: "goal_0", to: "tactic_1" },
        { from: "tactic_1", to: "hyp_2" },
        { from: "tactic_1", to: "goal_3" },
        { from: "goal_3", to: "tactic_4" },
        { from: "tactic_4", to: "goal_5" },
        { from: "goal_5", to: "tactic_6" },
        { from: "tactic_6", to: "tactic_7" },
        { from: "tactic_7", to: "qed_8" }
      ]
    },
    {
      name: "reachesPeriod2_iff_halts",
      file: "Discrete/HaltingToPeriodic.lean",
      description: "Halting ↔ reaching a period-2 orbit",
      statement: "tm.reachesPeriod2 cfg ↔ tm.halts cfg",
      nodes: [
        { id: "goal_0", type: "goal", label: "⊢ reachesPeriod2 ↔ halts", depth: 0 },
        { id: "tactic_1", type: "tactic", label: "constructor", depth: 1 },
        { id: "goal_2", type: "goal", label: "⊢ reachesPeriod2 → halts", depth: 2 },
        { id: "goal_3", type: "goal", label: "⊢ halts → reachesPeriod2", depth: 2 },
        { id: "tactic_4", type: "tactic", label: "intro ⟨n, hper⟩", depth: 2 },
        { id: "hyp_5", type: "hypothesis", label: "hper : IsPeriodicPt step 2 (stepN n cfg)", depth: 3 },
        { id: "tactic_6", type: "tactic", label: "exact halts_of_periodic hper", depth: 3 },
        { id: "tactic_7", type: "tactic", label: "intro ⟨n, hhalt⟩", depth: 2 },
        { id: "hyp_8", type: "hypothesis", label: "hhalt : isHalt (stepN n cfg)", depth: 3 },
        { id: "tactic_9", type: "tactic", label: "exact ⟨n, periodic_of_halt hhalt⟩", depth: 3 },
        { id: "qed_10", type: "qed", label: "QED", depth: 4 }
      ],
      edges: [
        { from: "goal_0", to: "tactic_1" },
        { from: "tactic_1", to: "goal_2" },
        { from: "tactic_1", to: "goal_3" },
        { from: "goal_2", to: "tactic_4" },
        { from: "tactic_4", to: "hyp_5" },
        { from: "hyp_5", to: "tactic_6" },
        { from: "goal_3", to: "tactic_7" },
        { from: "tactic_7", to: "hyp_8" },
        { from: "hyp_8", to: "tactic_9" },
        { from: "tactic_6", to: "qed_10" },
        { from: "tactic_9", to: "qed_10" }
      ]
    },
    {
      name: "ReachingRel.assoc",
      file: "TKFT/Reaching.lean",
      description: "Reaching relation composition is associative",
      statement: "(r ∘ᵣ s) ∘ᵣ t = r ∘ᵣ (s ∘ᵣ t)",
      nodes: [
        { id: "goal_0", type: "goal", label: "⊢ (r ∘ᵣ s) ∘ᵣ t = r ∘ᵣ (s ∘ᵣ t)", depth: 0 },
        { id: "tactic_1", type: "tactic", label: "ext x z", depth: 1 },
        { id: "goal_2", type: "goal", label: "⊢ ((r ∘ᵣ s) ∘ᵣ t).rel x z ↔ (r ∘ᵣ (s ∘ᵣ t)).rel x z", depth: 2 },
        { id: "tactic_3", type: "tactic", label: "simp only [comp_rel]", depth: 2 },
        { id: "goal_4", type: "goal", label: "⊢ (∃ y, (∃ w, r x w ∧ s w y) ∧ t y z) ↔ (∃ y, r x y ∧ ∃ w, s y w ∧ t w z)", depth: 3 },
        { id: "tactic_5", type: "tactic", label: "constructor", depth: 3 },
        { id: "tactic_6", type: "simp_trace", label: "rintro ⟨y, ⟨w, hrw, hwy⟩, hyz⟩", depth: 4 },
        { id: "tactic_7", type: "tactic", label: "exact ⟨w, hrw, y, hwy, hyz⟩", depth: 5 },
        { id: "tactic_8", type: "simp_trace", label: "rintro ⟨w, hrw, y, hwy, hyz⟩", depth: 4 },
        { id: "tactic_9", type: "tactic", label: "exact ⟨y, ⟨w, hrw, hwy⟩, hyz⟩", depth: 5 },
        { id: "qed_10", type: "qed", label: "QED", depth: 6 }
      ],
      edges: [
        { from: "goal_0", to: "tactic_1" },
        { from: "tactic_1", to: "goal_2" },
        { from: "goal_2", to: "tactic_3" },
        { from: "tactic_3", to: "goal_4" },
        { from: "goal_4", to: "tactic_5" },
        { from: "tactic_5", to: "tactic_6" },
        { from: "tactic_5", to: "tactic_8" },
        { from: "tactic_6", to: "tactic_7" },
        { from: "tactic_8", to: "tactic_9" },
        { from: "tactic_7", to: "qed_10" },
        { from: "tactic_9", to: "qed_10" }
      ]
    },
    {
      name: "isFixedPoint_unionNucleus_iff",
      file: "FixedPoint/PeriodicNucleus.lean",
      description: "Fixed points of union nucleus are supersets of U",
      statement: "IsFixedPoint (unionNucleus U) S ↔ U ⊆ S",
      nodes: [
        { id: "goal_0", type: "goal", label: "⊢ IsFixedPoint (unionNucleus U) S ↔ U ⊆ S", depth: 0 },
        { id: "tactic_1", type: "tactic", label: "simp only [IsFixedPoint, unionNucleus_apply]", depth: 1 },
        { id: "goal_2", type: "goal", label: "⊢ S ∪ U = S ↔ U ⊆ S", depth: 2 },
        { id: "tactic_3", type: "tactic", label: "constructor", depth: 2 },
        { id: "tactic_4", type: "tactic", label: "intro h", depth: 3 },
        { id: "goal_5", type: "goal", label: "⊢ U ⊆ S", depth: 3 },
        { id: "tactic_6", type: "tactic", label: "rw [← h]", depth: 4 },
        { id: "tactic_7", type: "tactic", label: "exact subset_union_right", depth: 4 },
        { id: "tactic_8", type: "tactic", label: "intro h", depth: 3 },
        { id: "goal_9", type: "goal", label: "⊢ S ∪ U = S", depth: 3 },
        { id: "tactic_10", type: "tactic", label: "exact union_eq_self_of_subset_right h", depth: 4 },
        { id: "qed_11", type: "qed", label: "QED", depth: 5 }
      ],
      edges: [
        { from: "goal_0", to: "tactic_1" },
        { from: "tactic_1", to: "goal_2" },
        { from: "goal_2", to: "tactic_3" },
        { from: "tactic_3", to: "tactic_4" },
        { from: "tactic_3", to: "tactic_8" },
        { from: "tactic_4", to: "goal_5" },
        { from: "goal_5", to: "tactic_6" },
        { from: "tactic_6", to: "tactic_7" },
        { from: "tactic_8", to: "goal_9" },
        { from: "goal_9", to: "tactic_10" },
        { from: "tactic_7", to: "qed_11" },
        { from: "tactic_10", to: "qed_11" }
      ]
    },
    {
      name: "not_computable_of_reduces",
      file: "Undecidability/Transfers.lean",
      description: "Undecidability transfers through reductions",
      statement: "¬Computable Q → Reduces P Q → ¬Computable P",
      nodes: [
        { id: "goal_0", type: "goal", label: "⊢ ¬Computable Q → Reduces P Q → ¬Computable P", depth: 0 },
        { id: "tactic_1", type: "tactic", label: "intro hQ hred hP", depth: 1 },
        { id: "hyp_2", type: "hypothesis", label: "hQ : ¬Computable Q", depth: 1 },
        { id: "hyp_3", type: "hypothesis", label: "hred : Reduces P Q", depth: 1 },
        { id: "hyp_4", type: "hypothesis", label: "hP : Computable P", depth: 1 },
        { id: "goal_5", type: "goal", label: "⊢ False", depth: 2 },
        { id: "tactic_6", type: "tactic", label: "apply hQ", depth: 2 },
        { id: "goal_7", type: "goal", label: "⊢ Computable Q", depth: 3 },
        { id: "tactic_8", type: "tactic", label: "exact computable_of_reduces hred hP", depth: 3 },
        { id: "qed_9", type: "qed", label: "QED", depth: 4 }
      ],
      edges: [
        { from: "goal_0", to: "tactic_1" },
        { from: "tactic_1", to: "hyp_2" },
        { from: "tactic_1", to: "hyp_3" },
        { from: "tactic_1", to: "hyp_4" },
        { from: "tactic_1", to: "goal_5" },
        { from: "goal_5", to: "tactic_6" },
        { from: "tactic_6", to: "goal_7" },
        { from: "goal_7", to: "tactic_8" },
        { from: "tactic_8", to: "qed_9" }
      ]
    }
  ]
};

if (typeof module !== 'undefined') {
  module.exports = tacticFlowData;
}
