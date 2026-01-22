// Miranda Dynamics Tactic Flow Data
// Key theorems with proof tactic traces (including Wolfram Physics theorems)
// Generated: 2026-01-21

const tacticFlowData = {
  theorems: [
    {
        "name": "encodeTape_injective",
        "file": "Billiards/CantorEncoding.lean",
        "description": "Cantor tape encoding is injective",
        "statement": "Function.Injective encodeTape",
        "nodes": [
            {
                "id": "goal_0",
                "type": "goal",
                "label": "\u22a2 Function.Injective encodeTape",
                "depth": 0
            },
            {
                "id": "tactic_1",
                "type": "tactic",
                "label": "intro t\u2081 t\u2082 h",
                "depth": 1
            },
            {
                "id": "hyp_2",
                "type": "hypothesis",
                "label": "h : encodeTape t\u2081 = encodeTape t\u2082",
                "depth": 1
            },
            {
                "id": "goal_3",
                "type": "goal",
                "label": "\u22a2 t\u2081 = t\u2082",
                "depth": 2
            },
            {
                "id": "tactic_4",
                "type": "tactic",
                "label": "ext k",
                "depth": 2
            },
            {
                "id": "goal_5",
                "type": "goal",
                "label": "\u22a2 t\u2081 k = t\u2082 k",
                "depth": 3
            },
            {
                "id": "tactic_6",
                "type": "tactic",
                "label": "apply digit_eq_of_encode_eq",
                "depth": 3
            },
            {
                "id": "tactic_7",
                "type": "tactic",
                "label": "exact h",
                "depth": 4
            },
            {
                "id": "qed_8",
                "type": "qed",
                "label": "QED",
                "depth": 5
            }
        ],
        "edges": [
            {
                "from": "goal_0",
                "to": "tactic_1"
            },
            {
                "from": "tactic_1",
                "to": "hyp_2"
            },
            {
                "from": "tactic_1",
                "to": "goal_3"
            },
            {
                "from": "goal_3",
                "to": "tactic_4"
            },
            {
                "from": "tactic_4",
                "to": "goal_5"
            },
            {
                "from": "goal_5",
                "to": "tactic_6"
            },
            {
                "from": "tactic_6",
                "to": "tactic_7"
            },
            {
                "from": "tactic_7",
                "to": "qed_8"
            }
        ]
    },
    {
        "name": "ReachingRel.assoc",
        "file": "TKFT/Reaching.lean",
        "description": "Reaching relation composition is associative",
        "statement": "(r \u2218\u1d63 s) \u2218\u1d63 t = r \u2218\u1d63 (s \u2218\u1d63 t)",
        "nodes": [
            {
                "id": "goal_0",
                "type": "goal",
                "label": "\u22a2 (r \u2218\u1d63 s) \u2218\u1d63 t = r \u2218\u1d63 (s \u2218\u1d63 t)",
                "depth": 0
            },
            {
                "id": "tactic_1",
                "type": "tactic",
                "label": "ext x z",
                "depth": 1
            },
            {
                "id": "goal_2",
                "type": "goal",
                "label": "\u22a2 ((r \u2218\u1d63 s) \u2218\u1d63 t).rel x z \u2194 ...",
                "depth": 2
            },
            {
                "id": "tactic_3",
                "type": "tactic",
                "label": "simp only [comp_rel]",
                "depth": 2
            },
            {
                "id": "tactic_4",
                "type": "tactic",
                "label": "constructor <;> rintro \u27e8...\u27e9",
                "depth": 3
            },
            {
                "id": "qed_5",
                "type": "qed",
                "label": "QED",
                "depth": 4
            }
        ],
        "edges": [
            {
                "from": "goal_0",
                "to": "tactic_1"
            },
            {
                "from": "tactic_1",
                "to": "goal_2"
            },
            {
                "from": "goal_2",
                "to": "tactic_3"
            },
            {
                "from": "tactic_3",
                "to": "tactic_4"
            },
            {
                "from": "tactic_4",
                "to": "qed_5"
            }
        ]
    },
    {
        "name": "JR.idem",
        "file": "WPP/Multiway.lean",
        "description": "Forward-invariance kernel JR is idempotent",
        "statement": "JR (JR U) = JR U",
        "nodes": [
            {
                "id": "goal_0",
                "type": "goal",
                "label": "\u22a2 JR (JR U) = JR U",
                "depth": 0
            },
            {
                "id": "tactic_1",
                "type": "tactic",
                "label": "ext s",
                "depth": 1
            },
            {
                "id": "goal_2",
                "type": "goal",
                "label": "\u22a2 JR (JR U) s \u2194 JR U s",
                "depth": 2
            },
            {
                "id": "tactic_3",
                "type": "tactic",
                "label": "constructor",
                "depth": 2
            },
            {
                "id": "tactic_4",
                "type": "tactic",
                "label": "intro hs t hst",
                "depth": 3
            },
            {
                "id": "tactic_5",
                "type": "tactic",
                "label": "exact (contractive (U := U)) (hs t hst)",
                "depth": 4
            },
            {
                "id": "tactic_6",
                "type": "tactic",
                "label": "intro hs t hst u htu",
                "depth": 3
            },
            {
                "id": "tactic_7",
                "type": "tactic",
                "label": "exact hs u (StepStar.trans hst htu)",
                "depth": 4
            },
            {
                "id": "qed_8",
                "type": "qed",
                "label": "QED",
                "depth": 5
            }
        ],
        "edges": [
            {
                "from": "goal_0",
                "to": "tactic_1"
            },
            {
                "from": "tactic_1",
                "to": "goal_2"
            },
            {
                "from": "goal_2",
                "to": "tactic_3"
            },
            {
                "from": "tactic_3",
                "to": "tactic_4"
            },
            {
                "from": "tactic_3",
                "to": "tactic_6"
            },
            {
                "from": "tactic_4",
                "to": "tactic_5"
            },
            {
                "from": "tactic_6",
                "to": "tactic_7"
            },
            {
                "from": "tactic_5",
                "to": "qed_8"
            },
            {
                "from": "tactic_7",
                "to": "qed_8"
            }
        ]
    },
    {
        "name": "StepStar.trans",
        "file": "WPP/Multiway.lean",
        "description": "Multiway step closure is transitive",
        "statement": "StepStar s t \u2192 StepStar t u \u2192 StepStar s u",
        "nodes": [
            {
                "id": "goal_0",
                "type": "goal",
                "label": "\u22a2 StepStar s t \u2192 StepStar t u \u2192 StepStar s u",
                "depth": 0
            },
            {
                "id": "tactic_1",
                "type": "tactic",
                "label": "intro hst htu",
                "depth": 1
            },
            {
                "id": "hyp_2",
                "type": "hypothesis",
                "label": "hst : StepStar s t",
                "depth": 1
            },
            {
                "id": "hyp_3",
                "type": "hypothesis",
                "label": "htu : StepStar t u",
                "depth": 1
            },
            {
                "id": "tactic_4",
                "type": "tactic",
                "label": "induction hst with",
                "depth": 2
            },
            {
                "id": "case_5",
                "type": "goal",
                "label": "| refl => simpa using htu",
                "depth": 3
            },
            {
                "id": "case_6",
                "type": "goal",
                "label": "| tail hstep hmid ih => exact StepStar.tail hstep (ih htu)",
                "depth": 3
            },
            {
                "id": "qed_7",
                "type": "qed",
                "label": "QED",
                "depth": 4
            }
        ],
        "edges": [
            {
                "from": "goal_0",
                "to": "tactic_1"
            },
            {
                "from": "tactic_1",
                "to": "hyp_2"
            },
            {
                "from": "tactic_1",
                "to": "hyp_3"
            },
            {
                "from": "hyp_3",
                "to": "tactic_4"
            },
            {
                "from": "tactic_4",
                "to": "case_5"
            },
            {
                "from": "tactic_4",
                "to": "case_6"
            },
            {
                "from": "case_5",
                "to": "qed_7"
            },
            {
                "from": "case_6",
                "to": "qed_7"
            }
        ]
    },
    {
        "name": "reachabilityNucleus.le_apply",
        "file": "WPP/Multiway.lean",
        "description": "Reachability nucleus is inflationary",
        "statement": "U \u2264 reachabilityNucleus s\u2080 U",
        "nodes": [
            {
                "id": "goal_0",
                "type": "goal",
                "label": "\u22a2 U \u2286 reachabilityNucleus s\u2080 U",
                "depth": 0
            },
            {
                "id": "tactic_1",
                "type": "tactic",
                "label": "intro s hs",
                "depth": 1
            },
            {
                "id": "hyp_2",
                "type": "hypothesis",
                "label": "hs : s \u2208 U",
                "depth": 1
            },
            {
                "id": "tactic_3",
                "type": "tactic",
                "label": "exact Or.inl hs",
                "depth": 2
            },
            {
                "id": "qed_4",
                "type": "qed",
                "label": "QED",
                "depth": 3
            }
        ],
        "edges": [
            {
                "from": "goal_0",
                "to": "tactic_1"
            },
            {
                "from": "tactic_1",
                "to": "hyp_2"
            },
            {
                "from": "hyp_2",
                "to": "tactic_3"
            },
            {
                "from": "tactic_3",
                "to": "qed_4"
            }
        ]
    },
    {
        "name": "isFixedPoint_unionNucleus_iff",
        "file": "FixedPoint/PeriodicNucleus.lean",
        "description": "Fixed points of union nucleus are supersets of U",
        "statement": "IsFixedPoint (unionNucleus U) S \u2194 U \u2286 S",
        "nodes": [
            {
                "id": "goal_0",
                "type": "goal",
                "label": "\u22a2 IsFixedPoint (unionNucleus U) S \u2194 U \u2286 S",
                "depth": 0
            },
            {
                "id": "tactic_1",
                "type": "tactic",
                "label": "simp only [IsFixedPoint, unionNucleus_apply]",
                "depth": 1
            },
            {
                "id": "goal_2",
                "type": "goal",
                "label": "\u22a2 S \u222a U = S \u2194 U \u2286 S",
                "depth": 2
            },
            {
                "id": "tactic_3",
                "type": "tactic",
                "label": "constructor",
                "depth": 2
            },
            {
                "id": "tactic_4",
                "type": "tactic",
                "label": "intro h; rw [\u2190 h]; exact subset_union_right",
                "depth": 3
            },
            {
                "id": "tactic_5",
                "type": "tactic",
                "label": "intro h; exact union_eq_self_of_subset_right h",
                "depth": 3
            },
            {
                "id": "qed_6",
                "type": "qed",
                "label": "QED",
                "depth": 4
            }
        ],
        "edges": [
            {
                "from": "goal_0",
                "to": "tactic_1"
            },
            {
                "from": "tactic_1",
                "to": "goal_2"
            },
            {
                "from": "goal_2",
                "to": "tactic_3"
            },
            {
                "from": "tactic_3",
                "to": "tactic_4"
            },
            {
                "from": "tactic_3",
                "to": "tactic_5"
            },
            {
                "from": "tactic_4",
                "to": "qed_6"
            },
            {
                "from": "tactic_5",
                "to": "qed_6"
            }
        ]
    }
]
};

if (typeof module !== 'undefined') {
  module.exports = tacticFlowData;
}
