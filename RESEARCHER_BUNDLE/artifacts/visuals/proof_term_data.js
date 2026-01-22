// Miranda Dynamics Proof Term DAG Data
// Abstract syntax tree of proof terms (including Wolfram Physics proofs)
// Generated: 2026-01-21

const proofTermData = {
  theorems: [
    {
        "name": "ReachingRel.comp",
        "file": "TKFT/Reaching.lean",
        "description": "Reaching relation composition",
        "statement": "ReachingRel \u03b1 \u03b2 \u2192 ReachingRel \u03b2 \u03b3 \u2192 ReachingRel \u03b1 \u03b3",
        "nodes": [
            {
                "id": "root",
                "type": "app",
                "label": "ReachingRel.mk",
                "depth": 0
            },
            {
                "id": "lam1",
                "type": "lam",
                "label": "fun a c =>",
                "depth": 1
            },
            {
                "id": "exists",
                "type": "app",
                "label": "\u2203 b, ...",
                "depth": 2
            },
            {
                "id": "and",
                "type": "app",
                "label": "R.rel a b \u2227 S.rel b c",
                "depth": 3
            },
            {
                "id": "rel_r",
                "type": "app",
                "label": "R.rel",
                "depth": 4
            },
            {
                "id": "rel_s",
                "type": "app",
                "label": "S.rel",
                "depth": 4
            }
        ],
        "edges": [
            {
                "from": "root",
                "to": "lam1"
            },
            {
                "from": "lam1",
                "to": "exists"
            },
            {
                "from": "exists",
                "to": "and"
            },
            {
                "from": "and",
                "to": "rel_r"
            },
            {
                "from": "and",
                "to": "rel_s"
            }
        ]
    },
    {
        "name": "JR.mono",
        "file": "WPP/Multiway.lean",
        "description": "Forward-invariance kernel is monotone",
        "statement": "Monotone JR",
        "nodes": [
            {
                "id": "root",
                "type": "lam",
                "label": "fun U V hUV s hs =>",
                "depth": 0
            },
            {
                "id": "intro",
                "type": "app",
                "label": "intro t hst",
                "depth": 1
            },
            {
                "id": "app_huv",
                "type": "app",
                "label": "hUV (hs _ hst)",
                "depth": 2
            },
            {
                "id": "hs",
                "type": "var",
                "label": "hs",
                "depth": 3
            },
            {
                "id": "hst",
                "type": "var",
                "label": "hst",
                "depth": 3
            }
        ],
        "edges": [
            {
                "from": "root",
                "to": "intro"
            },
            {
                "from": "intro",
                "to": "app_huv"
            },
            {
                "from": "app_huv",
                "to": "hs"
            },
            {
                "from": "app_huv",
                "to": "hst"
            }
        ]
    },
    {
        "name": "reachabilityNucleus",
        "file": "WPP/Multiway.lean",
        "description": "Inflationary nucleus from multiway reachability",
        "statement": "Nucleus (Set State)",
        "nodes": [
            {
                "id": "root",
                "type": "mk",
                "label": "Nucleus.mk",
                "depth": 0
            },
            {
                "id": "tofun",
                "type": "lam",
                "label": "toFun := fun U => U \u222a unreachableFrom s\u2080",
                "depth": 1
            },
            {
                "id": "map_inf",
                "type": "app",
                "label": "map_inf' := ...",
                "depth": 1
            },
            {
                "id": "idem",
                "type": "app",
                "label": "idempotent' := ...",
                "depth": 1
            },
            {
                "id": "le_apply",
                "type": "app",
                "label": "le_apply' := fun s hs => Or.inl hs",
                "depth": 1
            },
            {
                "id": "union",
                "type": "app",
                "label": "U \u222a unreachableFrom s\u2080",
                "depth": 2
            },
            {
                "id": "U",
                "type": "var",
                "label": "U",
                "depth": 3
            },
            {
                "id": "unreach",
                "type": "app",
                "label": "unreachableFrom s\u2080",
                "depth": 3
            }
        ],
        "edges": [
            {
                "from": "root",
                "to": "tofun"
            },
            {
                "from": "root",
                "to": "map_inf"
            },
            {
                "from": "root",
                "to": "idem"
            },
            {
                "from": "root",
                "to": "le_apply"
            },
            {
                "from": "tofun",
                "to": "union"
            },
            {
                "from": "union",
                "to": "U"
            },
            {
                "from": "union",
                "to": "unreach"
            }
        ]
    },
    {
        "name": "StepStar.trans",
        "file": "WPP/Multiway.lean",
        "description": "Transitivity of step closure",
        "statement": "StepStar s t \u2192 StepStar t u \u2192 StepStar s u",
        "nodes": [
            {
                "id": "root",
                "type": "lam",
                "label": "fun hst htu =>",
                "depth": 0
            },
            {
                "id": "ind",
                "type": "app",
                "label": "induction hst",
                "depth": 1
            },
            {
                "id": "refl",
                "type": "app",
                "label": "| refl => htu",
                "depth": 2
            },
            {
                "id": "tail",
                "type": "app",
                "label": "| tail hstep hmid ih =>",
                "depth": 2
            },
            {
                "id": "rec",
                "type": "app",
                "label": "StepStar.tail hstep (ih htu)",
                "depth": 3
            },
            {
                "id": "hstep",
                "type": "var",
                "label": "hstep",
                "depth": 4
            },
            {
                "id": "ih_app",
                "type": "app",
                "label": "ih htu",
                "depth": 4
            }
        ],
        "edges": [
            {
                "from": "root",
                "to": "ind"
            },
            {
                "from": "ind",
                "to": "refl"
            },
            {
                "from": "ind",
                "to": "tail"
            },
            {
                "from": "tail",
                "to": "rec"
            },
            {
                "from": "rec",
                "to": "hstep"
            },
            {
                "from": "rec",
                "to": "ih_app"
            }
        ]
    },
    {
        "name": "cantorNucleus_fixed_iff",
        "file": "Billiards/CantorEncoding.lean",
        "description": "Fixed points of Cantor nucleus",
        "statement": "IsFixedPoint cantorNucleus S \u2194 \u2200 t, encodeTape t \u2208 S",
        "nodes": [
            {
                "id": "root",
                "type": "app",
                "label": "Iff.intro",
                "depth": 0
            },
            {
                "id": "mp",
                "type": "lam",
                "label": "fun h t =>",
                "depth": 1
            },
            {
                "id": "mpr",
                "type": "lam",
                "label": "fun h =>",
                "depth": 1
            },
            {
                "id": "mp_body",
                "type": "app",
                "label": "h \u25b8 Or.inl (mem_range_self t)",
                "depth": 2
            },
            {
                "id": "mpr_body",
                "type": "app",
                "label": "eq_of_subset_of_subset ...",
                "depth": 2
            }
        ],
        "edges": [
            {
                "from": "root",
                "to": "mp"
            },
            {
                "from": "root",
                "to": "mpr"
            },
            {
                "from": "mp",
                "to": "mp_body"
            },
            {
                "from": "mpr",
                "to": "mpr_body"
            }
        ]
    }
]
};

if (typeof module !== 'undefined') {
  module.exports = proofTermData;
}
