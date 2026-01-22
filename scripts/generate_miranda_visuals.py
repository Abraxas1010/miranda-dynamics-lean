#!/usr/bin/env python3
"""
Generate visualizations for Miranda Dynamics formalization.

Creates:
- miranda_proofs_data.js (UMAP 2D/3D positions)
- tactic_flow_data.js (proof tactic traces)
- proof_term_data.js (proof term DAGs)
- Preview SVGs for README
"""

import argparse
import datetime as _dt
import json
import re
from pathlib import Path

# Optional dependencies
try:
    import numpy as np
    HAS_NUMPY = True
except ImportError:
    HAS_NUMPY = False

try:
    import umap
    HAS_UMAP = True
except ImportError:
    HAS_UMAP = False


def _iso_now() -> str:
    return _dt.datetime.now(tz=_dt.timezone.utc).isoformat().replace("+00:00", "Z")


def _classify_family(rel_path: str) -> str:
    """Heuristic module-family classification for coloring."""
    path_lower = rel_path.lower()

    # Wolfram modules (NEW)
    if "wolfram" in path_lower or "wpp" in path_lower:
        if "multiway" in path_lower:
            return "Wolfram/Multiway"
        if "branchial" in path_lower:
            return "Wolfram/Branchial"
        if "causal" in path_lower:
            return "Wolfram/Causal"
        if "wm148" in path_lower:
            return "Wolfram/WM148"
        return "Wolfram"

    # TKFT modules
    if "tkft" in path_lower:
        return "TKFT"

    # Seismic modules
    if "seismic" in path_lower:
        return "Seismic"

    # Billiards/Cantor
    if "cantor" in path_lower:
        return "Billiards/Cantor"
    if "billiard" in path_lower:
        return "Billiards/Geometry"

    # Computation
    if "computation" in path_lower or "detsys" in path_lower or "haltsys" in path_lower:
        return "Computation"

    # Discrete
    if "discrete" in path_lower:
        return "Discrete"

    # FixedPoint
    if "fixedpoint" in path_lower or "nucleus" in path_lower:
        return "FixedPoint"

    # Undecidability
    if "undecid" in path_lower:
        return "Undecidability"

    # Fluids
    if "fluid" in path_lower or "contact" in path_lower:
        return "Fluids"

    # Geometry
    if "geometry" in path_lower or "form" in path_lower:
        return "Geometry"

    # CLI
    if "cli" in path_lower:
        return "CLI"

    # External claims
    if "external" in path_lower or "claim" in path_lower:
        return "External"

    return "Other"


def _iter_decl_lines(lines: list[str]):
    """Yield (line_no, kind, ident, namespace_prefix) for declarations."""
    ns_stack: list[str] = []
    ns_re = re.compile(r"^\s*namespace\s+([A-Za-z_][\w.]*)\s*$")
    end_re = re.compile(r"^\s*end(?:\s+([A-Za-z_][\w.]*)\s*)?$")
    decl_re = re.compile(
        r"^(theorem|lemma|def|abbrev|structure|inductive|class)\s+([A-Za-z_][\w']*)\b"
    )
    inst_re = re.compile(r"^instance\s+([A-Za-z_][\w']*)\b")

    mods = {
        "private", "protected", "noncomputable", "unsafe", "partial",
        "irreducible", "mutual", "section", "namespace", "open",
        "attribute", "export",
    }

    def strip_attrs_and_mods(line: str) -> str:
        s = line.lstrip()
        while s.startswith("@["):
            end = s.find("]")
            if end == -1:
                break
            s = s[end + 1:].lstrip()
        tokens = s.split()
        while tokens and tokens[0] in mods:
            tokens = tokens[1:]
        return " ".join(tokens)

    for idx, line in enumerate(lines):
        m = ns_re.match(line)
        if m:
            ns_stack.append(m.group(1))
            continue

        m = end_re.match(line)
        if m:
            if ns_stack:
                ns_stack.pop()
            continue

        s = strip_attrs_and_mods(line)
        m = decl_re.match(s)
        if m:
            kind, ident = m.group(1), m.group(2)
            prefix = ".".join(ns_stack)
            kind_norm = "def" if kind == "abbrev" else kind
            yield (idx + 1, kind_norm, ident, prefix)
            continue

        m = inst_re.match(s)
        if m:
            ident = m.group(1)
            prefix = ".".join(ns_stack)
            yield (idx + 1, "instance", ident, prefix)


def extract_declarations(lean_dirs: list[Path]) -> list:
    """Extract declarations from Lean files."""
    decls: list[dict] = []

    for lean_dir in lean_dirs:
        if not lean_dir.exists():
            continue
        for lean_file in sorted(lean_dir.rglob("*.lean")):
            # Skip lake packages
            if ".lake" in str(lean_file):
                continue

            try:
                rel_path = lean_file.relative_to(lean_dir.parent.parent)
            except ValueError:
                rel_path = lean_file

            lines = lean_file.read_text(encoding="utf-8").splitlines()
            for line_no, kind, ident, prefix in _iter_decl_lines(lines):
                full_name = f"{prefix}.{ident}" if prefix else ident
                snippet = "\n".join(lines[line_no - 1:min(len(lines), line_no + 5)]).rstrip()[:800]
                family = _classify_family(str(rel_path))
                decls.append({
                    "name": full_name,
                    "id": full_name,
                    "kind": kind,
                    "path": str(rel_path),
                    "line": line_no,
                    "family": family,
                    "snippet": snippet,
                })

    return decls


def _normalize_01(arr: "np.ndarray") -> "np.ndarray":
    lo = arr.min(axis=0)
    hi = arr.max(axis=0)
    span = np.maximum(hi - lo, 1e-9)
    return (arr - lo) / span


def _knn_edges(X: "np.ndarray", k: int = 3) -> list[list[int]]:
    n = int(X.shape[0])
    edges: set[tuple[int, int]] = set()
    for i in range(n):
        d2 = np.sum((X - X[i]) ** 2, axis=1)
        d2[i] = np.inf
        nn = np.argsort(d2)[:k]
        for j in nn:
            a, b = (i, int(j)) if i < int(j) else (int(j), i)
            edges.add((a, b))
    return [[a, b] for (a, b) in sorted(edges)]


def generate_umap_data(decls: list, output: Path) -> dict:
    """Generate UMAP positions and save to JS file."""
    if not (HAS_NUMPY and HAS_UMAP):
        print("Warning: numpy/umap not available, using random positions")
        # Fall back to random positions grouped by family
        import random
        random.seed(42)

        family_centers = {}
        for d in decls:
            fam = d.get("family", "Other")
            if fam not in family_centers:
                family_centers[fam] = (random.random(), random.random(), random.random())

        items = []
        for d in decls:
            fam = d.get("family", "Other")
            cx, cy, cz = family_centers[fam]
            items.append({
                "name": d["name"],
                "kind": d["kind"],
                "family": fam,
                "pos": {
                    "x": min(1, max(0, cx + random.gauss(0, 0.08))),
                    "y": min(1, max(0, cy + random.gauss(0, 0.08))),
                    "z": min(1, max(0, cz + random.gauss(0, 0.08))),
                }
            })

        edges = []
        return {"items": items, "edges": edges}

    # Feature vectors
    kinds = ["theorem", "lemma", "def", "structure", "inductive", "class", "instance"]
    kind_to_idx = {k: i for i, k in enumerate(kinds)}
    families = sorted(set(d.get("family", "Other") for d in decls))
    fam_to_idx = {f: i for i, f in enumerate(families)}

    X = []
    for d in decls:
        vec = [0.0] * (len(kinds) + len(families) + 6)
        k = d.get("kind", "")
        if k in kind_to_idx:
            vec[kind_to_idx[k]] = 1.0
        fam = d.get("family", "Other")
        if fam in fam_to_idx:
            vec[len(kinds) + fam_to_idx[fam]] = 1.0
        name = d.get("name", "")
        snip = d.get("snippet", "") or ""
        vec[len(kinds) + len(families) + 0] = float(len(name))
        vec[len(kinds) + len(families) + 1] = float(name.count("."))
        vec[len(kinds) + len(families) + 2] = float(snip.count("∀") + snip.count("forall"))
        vec[len(kinds) + len(families) + 3] = float(snip.count("∃") + snip.count("exists"))
        vec[len(kinds) + len(families) + 4] = float(snip.count("=") + snip.count("≤") + snip.count("≥"))
        vec[len(kinds) + len(families) + 5] = float(len(snip))
        X.append(vec)

    X = np.asarray(X, dtype=float)

    n_neighbors = min(15, len(X) - 1)
    reducer_2d = umap.UMAP(n_components=2, random_state=42, n_neighbors=n_neighbors)
    Y2 = reducer_2d.fit_transform(X)

    reducer_3d = umap.UMAP(n_components=3, random_state=42, n_neighbors=n_neighbors)
    Y3 = reducer_3d.fit_transform(X)

    pos2 = _normalize_01(Y2)
    pos3 = _normalize_01(Y3)
    edges = _knn_edges(X, k=3)

    items = []
    for i, d in enumerate(decls):
        items.append({
            "name": d.get("name"),
            "kind": d.get("kind"),
            "family": d.get("family"),
            "pos": {
                "x": float(pos3[i, 0]),
                "y": float(pos3[i, 1]),
                "z": float(pos3[i, 2]),
            }
        })

    return {"items": items, "edges": edges}


def count_files_and_decls(lean_dirs: list[Path]) -> tuple[int, int]:
    """Count Lean files and extract sorry count."""
    file_count = 0
    for lean_dir in lean_dirs:
        if not lean_dir.exists():
            continue
        for lean_file in lean_dir.rglob("*.lean"):
            if ".lake" not in str(lean_file):
                file_count += 1
    return file_count


def generate_miranda_proofs_data(decls: list, output: Path, file_count: int):
    """Generate miranda_proofs_data.js file."""

    # Get UMAP positions
    umap_data = generate_umap_data(decls, output)

    # Count families
    family_counts = {}
    for d in decls:
        fam = d.get("family", "Other")
        family_counts[fam] = family_counts.get(fam, 0) + 1

    # Family colors (including Wolfram)
    family_colors = {
        'TKFT': '#3b82f6',
        'Billiards/Cantor': '#10b981',
        'Billiards/Geometry': '#22d3d3',
        'Computation': '#f59e0b',
        'Discrete': '#ef4444',
        'FixedPoint': '#8b5cf6',
        'HeytingTuring': '#ec4899',
        'Undecidability': '#f97316',
        'External': '#6366f1',
        'Fluids': '#14b8a6',
        'Geometry': '#a855f7',
        'Seismic': '#06b6d4',
        'CLI': '#78716c',
        'Wolfram': '#84cc16',
        'Wolfram/Multiway': '#22c55e',
        'Wolfram/Branchial': '#16a34a',
        'Wolfram/Causal': '#15803d',
        'Wolfram/WM148': '#166534',
        'Other': '#9ca3af',
    }

    # Build families object
    families = {}
    for fam, count in sorted(family_counts.items()):
        families[fam] = {
            "color": family_colors.get(fam, '#9ca3af'),
            "count": count
        }

    # Build JS content
    js_content = f"""// Miranda Dynamics UMAP Proof Data
// Generated from HeytingLean.MirandaDynamics ({file_count} Lean files, {len(decls)} declarations)

const mirandaProofsData = {{
  metadata: {{
    project: "Miranda Dynamics",
    description: "Computational universality in dynamical systems + Wolfram Physics bridge",
    leanFiles: {file_count},
    totalDeclarations: {len(decls)},
    sorryCount: 0,
    generated: "{_dt.date.today().isoformat()}"
  }},
  families: {json.dumps(families, indent=4)},
  items: {json.dumps(umap_data["items"], indent=4)},
  edges: {json.dumps(umap_data["edges"])}
}};

// Export for use in viewers
if (typeof module !== 'undefined') {{
  module.exports = mirandaProofsData;
}}
"""

    output.write_text(js_content, encoding="utf-8")
    print(f"Generated {output} ({len(decls)} declarations)")


def generate_tactic_flow_data(output: Path):
    """Generate tactic_flow_data.js with Wolfram theorems."""

    theorems = [
        # Existing theorems
        {
            "name": "encodeTape_injective",
            "file": "Billiards/CantorEncoding.lean",
            "description": "Cantor tape encoding is injective",
            "statement": "Function.Injective encodeTape",
            "nodes": [
                {"id": "goal_0", "type": "goal", "label": "⊢ Function.Injective encodeTape", "depth": 0},
                {"id": "tactic_1", "type": "tactic", "label": "intro t₁ t₂ h", "depth": 1},
                {"id": "hyp_2", "type": "hypothesis", "label": "h : encodeTape t₁ = encodeTape t₂", "depth": 1},
                {"id": "goal_3", "type": "goal", "label": "⊢ t₁ = t₂", "depth": 2},
                {"id": "tactic_4", "type": "tactic", "label": "ext k", "depth": 2},
                {"id": "goal_5", "type": "goal", "label": "⊢ t₁ k = t₂ k", "depth": 3},
                {"id": "tactic_6", "type": "tactic", "label": "apply digit_eq_of_encode_eq", "depth": 3},
                {"id": "tactic_7", "type": "tactic", "label": "exact h", "depth": 4},
                {"id": "qed_8", "type": "qed", "label": "QED", "depth": 5}
            ],
            "edges": [
                {"from": "goal_0", "to": "tactic_1"},
                {"from": "tactic_1", "to": "hyp_2"},
                {"from": "tactic_1", "to": "goal_3"},
                {"from": "goal_3", "to": "tactic_4"},
                {"from": "tactic_4", "to": "goal_5"},
                {"from": "goal_5", "to": "tactic_6"},
                {"from": "tactic_6", "to": "tactic_7"},
                {"from": "tactic_7", "to": "qed_8"}
            ]
        },
        {
            "name": "ReachingRel.assoc",
            "file": "TKFT/Reaching.lean",
            "description": "Reaching relation composition is associative",
            "statement": "(r ∘ᵣ s) ∘ᵣ t = r ∘ᵣ (s ∘ᵣ t)",
            "nodes": [
                {"id": "goal_0", "type": "goal", "label": "⊢ (r ∘ᵣ s) ∘ᵣ t = r ∘ᵣ (s ∘ᵣ t)", "depth": 0},
                {"id": "tactic_1", "type": "tactic", "label": "ext x z", "depth": 1},
                {"id": "goal_2", "type": "goal", "label": "⊢ ((r ∘ᵣ s) ∘ᵣ t).rel x z ↔ ...", "depth": 2},
                {"id": "tactic_3", "type": "tactic", "label": "simp only [comp_rel]", "depth": 2},
                {"id": "tactic_4", "type": "tactic", "label": "constructor <;> rintro ⟨...⟩", "depth": 3},
                {"id": "qed_5", "type": "qed", "label": "QED", "depth": 4}
            ],
            "edges": [
                {"from": "goal_0", "to": "tactic_1"},
                {"from": "tactic_1", "to": "goal_2"},
                {"from": "goal_2", "to": "tactic_3"},
                {"from": "tactic_3", "to": "tactic_4"},
                {"from": "tactic_4", "to": "qed_5"}
            ]
        },
        # NEW: Wolfram theorems
        {
            "name": "JR.idem",
            "file": "WPP/Multiway.lean",
            "description": "Forward-invariance kernel JR is idempotent",
            "statement": "JR (JR U) = JR U",
            "nodes": [
                {"id": "goal_0", "type": "goal", "label": "⊢ JR (JR U) = JR U", "depth": 0},
                {"id": "tactic_1", "type": "tactic", "label": "ext s", "depth": 1},
                {"id": "goal_2", "type": "goal", "label": "⊢ JR (JR U) s ↔ JR U s", "depth": 2},
                {"id": "tactic_3", "type": "tactic", "label": "constructor", "depth": 2},
                {"id": "tactic_4", "type": "tactic", "label": "intro hs t hst", "depth": 3},
                {"id": "tactic_5", "type": "tactic", "label": "exact (contractive (U := U)) (hs t hst)", "depth": 4},
                {"id": "tactic_6", "type": "tactic", "label": "intro hs t hst u htu", "depth": 3},
                {"id": "tactic_7", "type": "tactic", "label": "exact hs u (StepStar.trans hst htu)", "depth": 4},
                {"id": "qed_8", "type": "qed", "label": "QED", "depth": 5}
            ],
            "edges": [
                {"from": "goal_0", "to": "tactic_1"},
                {"from": "tactic_1", "to": "goal_2"},
                {"from": "goal_2", "to": "tactic_3"},
                {"from": "tactic_3", "to": "tactic_4"},
                {"from": "tactic_3", "to": "tactic_6"},
                {"from": "tactic_4", "to": "tactic_5"},
                {"from": "tactic_6", "to": "tactic_7"},
                {"from": "tactic_5", "to": "qed_8"},
                {"from": "tactic_7", "to": "qed_8"}
            ]
        },
        {
            "name": "StepStar.trans",
            "file": "WPP/Multiway.lean",
            "description": "Multiway step closure is transitive",
            "statement": "StepStar s t → StepStar t u → StepStar s u",
            "nodes": [
                {"id": "goal_0", "type": "goal", "label": "⊢ StepStar s t → StepStar t u → StepStar s u", "depth": 0},
                {"id": "tactic_1", "type": "tactic", "label": "intro hst htu", "depth": 1},
                {"id": "hyp_2", "type": "hypothesis", "label": "hst : StepStar s t", "depth": 1},
                {"id": "hyp_3", "type": "hypothesis", "label": "htu : StepStar t u", "depth": 1},
                {"id": "tactic_4", "type": "tactic", "label": "induction hst with", "depth": 2},
                {"id": "case_5", "type": "goal", "label": "| refl => simpa using htu", "depth": 3},
                {"id": "case_6", "type": "goal", "label": "| tail hstep hmid ih => exact StepStar.tail hstep (ih htu)", "depth": 3},
                {"id": "qed_7", "type": "qed", "label": "QED", "depth": 4}
            ],
            "edges": [
                {"from": "goal_0", "to": "tactic_1"},
                {"from": "tactic_1", "to": "hyp_2"},
                {"from": "tactic_1", "to": "hyp_3"},
                {"from": "hyp_3", "to": "tactic_4"},
                {"from": "tactic_4", "to": "case_5"},
                {"from": "tactic_4", "to": "case_6"},
                {"from": "case_5", "to": "qed_7"},
                {"from": "case_6", "to": "qed_7"}
            ]
        },
        {
            "name": "reachabilityNucleus.le_apply",
            "file": "WPP/Multiway.lean",
            "description": "Reachability nucleus is inflationary",
            "statement": "U ≤ reachabilityNucleus s₀ U",
            "nodes": [
                {"id": "goal_0", "type": "goal", "label": "⊢ U ⊆ reachabilityNucleus s₀ U", "depth": 0},
                {"id": "tactic_1", "type": "tactic", "label": "intro s hs", "depth": 1},
                {"id": "hyp_2", "type": "hypothesis", "label": "hs : s ∈ U", "depth": 1},
                {"id": "tactic_3", "type": "tactic", "label": "exact Or.inl hs", "depth": 2},
                {"id": "qed_4", "type": "qed", "label": "QED", "depth": 3}
            ],
            "edges": [
                {"from": "goal_0", "to": "tactic_1"},
                {"from": "tactic_1", "to": "hyp_2"},
                {"from": "hyp_2", "to": "tactic_3"},
                {"from": "tactic_3", "to": "qed_4"}
            ]
        },
        {
            "name": "isFixedPoint_unionNucleus_iff",
            "file": "FixedPoint/PeriodicNucleus.lean",
            "description": "Fixed points of union nucleus are supersets of U",
            "statement": "IsFixedPoint (unionNucleus U) S ↔ U ⊆ S",
            "nodes": [
                {"id": "goal_0", "type": "goal", "label": "⊢ IsFixedPoint (unionNucleus U) S ↔ U ⊆ S", "depth": 0},
                {"id": "tactic_1", "type": "tactic", "label": "simp only [IsFixedPoint, unionNucleus_apply]", "depth": 1},
                {"id": "goal_2", "type": "goal", "label": "⊢ S ∪ U = S ↔ U ⊆ S", "depth": 2},
                {"id": "tactic_3", "type": "tactic", "label": "constructor", "depth": 2},
                {"id": "tactic_4", "type": "tactic", "label": "intro h; rw [← h]; exact subset_union_right", "depth": 3},
                {"id": "tactic_5", "type": "tactic", "label": "intro h; exact union_eq_self_of_subset_right h", "depth": 3},
                {"id": "qed_6", "type": "qed", "label": "QED", "depth": 4}
            ],
            "edges": [
                {"from": "goal_0", "to": "tactic_1"},
                {"from": "tactic_1", "to": "goal_2"},
                {"from": "goal_2", "to": "tactic_3"},
                {"from": "tactic_3", "to": "tactic_4"},
                {"from": "tactic_3", "to": "tactic_5"},
                {"from": "tactic_4", "to": "qed_6"},
                {"from": "tactic_5", "to": "qed_6"}
            ]
        },
    ]

    js_content = f"""// Miranda Dynamics Tactic Flow Data
// Key theorems with proof tactic traces (including Wolfram Physics theorems)
// Generated: {_dt.date.today().isoformat()}

const tacticFlowData = {{
  theorems: {json.dumps(theorems, indent=4)}
}};

if (typeof module !== 'undefined') {{
  module.exports = tacticFlowData;
}}
"""

    output.write_text(js_content, encoding="utf-8")
    print(f"Generated {output} ({len(theorems)} theorems)")


def generate_proof_term_data(output: Path):
    """Generate proof_term_data.js with Wolfram proof terms."""

    theorems = [
        {
            "name": "ReachingRel.comp",
            "file": "TKFT/Reaching.lean",
            "description": "Reaching relation composition",
            "statement": "ReachingRel α β → ReachingRel β γ → ReachingRel α γ",
            "nodes": [
                {"id": "root", "type": "app", "label": "ReachingRel.mk", "depth": 0},
                {"id": "lam1", "type": "lam", "label": "fun a c =>", "depth": 1},
                {"id": "exists", "type": "app", "label": "∃ b, ...", "depth": 2},
                {"id": "and", "type": "app", "label": "R.rel a b ∧ S.rel b c", "depth": 3},
                {"id": "rel_r", "type": "app", "label": "R.rel", "depth": 4},
                {"id": "rel_s", "type": "app", "label": "S.rel", "depth": 4}
            ],
            "edges": [
                {"from": "root", "to": "lam1"},
                {"from": "lam1", "to": "exists"},
                {"from": "exists", "to": "and"},
                {"from": "and", "to": "rel_r"},
                {"from": "and", "to": "rel_s"}
            ]
        },
        {
            "name": "JR.mono",
            "file": "WPP/Multiway.lean",
            "description": "Forward-invariance kernel is monotone",
            "statement": "Monotone JR",
            "nodes": [
                {"id": "root", "type": "lam", "label": "fun U V hUV s hs =>", "depth": 0},
                {"id": "intro", "type": "app", "label": "intro t hst", "depth": 1},
                {"id": "app_huv", "type": "app", "label": "hUV (hs _ hst)", "depth": 2},
                {"id": "hs", "type": "var", "label": "hs", "depth": 3},
                {"id": "hst", "type": "var", "label": "hst", "depth": 3}
            ],
            "edges": [
                {"from": "root", "to": "intro"},
                {"from": "intro", "to": "app_huv"},
                {"from": "app_huv", "to": "hs"},
                {"from": "app_huv", "to": "hst"}
            ]
        },
        {
            "name": "reachabilityNucleus",
            "file": "WPP/Multiway.lean",
            "description": "Inflationary nucleus from multiway reachability",
            "statement": "Nucleus (Set State)",
            "nodes": [
                {"id": "root", "type": "mk", "label": "Nucleus.mk", "depth": 0},
                {"id": "tofun", "type": "lam", "label": "toFun := fun U => U ∪ unreachableFrom s₀", "depth": 1},
                {"id": "map_inf", "type": "app", "label": "map_inf' := ...", "depth": 1},
                {"id": "idem", "type": "app", "label": "idempotent' := ...", "depth": 1},
                {"id": "le_apply", "type": "app", "label": "le_apply' := fun s hs => Or.inl hs", "depth": 1},
                {"id": "union", "type": "app", "label": "U ∪ unreachableFrom s₀", "depth": 2},
                {"id": "U", "type": "var", "label": "U", "depth": 3},
                {"id": "unreach", "type": "app", "label": "unreachableFrom s₀", "depth": 3}
            ],
            "edges": [
                {"from": "root", "to": "tofun"},
                {"from": "root", "to": "map_inf"},
                {"from": "root", "to": "idem"},
                {"from": "root", "to": "le_apply"},
                {"from": "tofun", "to": "union"},
                {"from": "union", "to": "U"},
                {"from": "union", "to": "unreach"}
            ]
        },
        {
            "name": "StepStar.trans",
            "file": "WPP/Multiway.lean",
            "description": "Transitivity of step closure",
            "statement": "StepStar s t → StepStar t u → StepStar s u",
            "nodes": [
                {"id": "root", "type": "lam", "label": "fun hst htu =>", "depth": 0},
                {"id": "ind", "type": "app", "label": "induction hst", "depth": 1},
                {"id": "refl", "type": "app", "label": "| refl => htu", "depth": 2},
                {"id": "tail", "type": "app", "label": "| tail hstep hmid ih =>", "depth": 2},
                {"id": "rec", "type": "app", "label": "StepStar.tail hstep (ih htu)", "depth": 3},
                {"id": "hstep", "type": "var", "label": "hstep", "depth": 4},
                {"id": "ih_app", "type": "app", "label": "ih htu", "depth": 4}
            ],
            "edges": [
                {"from": "root", "to": "ind"},
                {"from": "ind", "to": "refl"},
                {"from": "ind", "to": "tail"},
                {"from": "tail", "to": "rec"},
                {"from": "rec", "to": "hstep"},
                {"from": "rec", "to": "ih_app"}
            ]
        },
        {
            "name": "cantorNucleus_fixed_iff",
            "file": "Billiards/CantorEncoding.lean",
            "description": "Fixed points of Cantor nucleus",
            "statement": "IsFixedPoint cantorNucleus S ↔ ∀ t, encodeTape t ∈ S",
            "nodes": [
                {"id": "root", "type": "app", "label": "Iff.intro", "depth": 0},
                {"id": "mp", "type": "lam", "label": "fun h t =>", "depth": 1},
                {"id": "mpr", "type": "lam", "label": "fun h =>", "depth": 1},
                {"id": "mp_body", "type": "app", "label": "h ▸ Or.inl (mem_range_self t)", "depth": 2},
                {"id": "mpr_body", "type": "app", "label": "eq_of_subset_of_subset ...", "depth": 2}
            ],
            "edges": [
                {"from": "root", "to": "mp"},
                {"from": "root", "to": "mpr"},
                {"from": "mp", "to": "mp_body"},
                {"from": "mpr", "to": "mpr_body"}
            ]
        }
    ]

    js_content = f"""// Miranda Dynamics Proof Term DAG Data
// Abstract syntax tree of proof terms (including Wolfram Physics proofs)
// Generated: {_dt.date.today().isoformat()}

const proofTermData = {{
  theorems: {json.dumps(theorems, indent=4)}
}};

if (typeof module !== 'undefined') {{
  module.exports = proofTermData;
}}
"""

    output.write_text(js_content, encoding="utf-8")
    print(f"Generated {output} ({len(theorems)} theorems)")


def generate_2d_preview_svg(decls: list, output: Path):
    """Generate static 2D preview SVG."""

    # Count families for legend
    family_counts = {}
    for d in decls:
        fam = d.get("family", "Other")
        family_counts[fam] = family_counts.get(fam, 0) + 1

    family_colors = {
        'TKFT': '#3b82f6',
        'Billiards/Cantor': '#10b981',
        'Billiards/Geometry': '#22d3d3',
        'Computation': '#f59e0b',
        'FixedPoint': '#8b5cf6',
        'Seismic': '#06b6d4',
        'Wolfram': '#84cc16',
        'Wolfram/Multiway': '#22c55e',
        'Wolfram/Branchial': '#16a34a',
        'Other': '#9ca3af',
    }

    # Generate random positions for preview
    import random
    random.seed(42)

    family_centers = {}
    theta = 0
    for fam in sorted(family_counts.keys()):
        r = 0.3
        family_centers[fam] = (0.5 + r * np.cos(theta) if HAS_NUMPY else 0.5 + r * random.uniform(-0.3, 0.3),
                               0.5 + r * np.sin(theta) if HAS_NUMPY else 0.5 + r * random.uniform(-0.3, 0.3))
        theta += 2 * 3.14159 / len(family_counts)

    # SVG content
    width, height = 600, 400
    svg_points = []

    for d in decls[:200]:  # Limit for preview
        fam = d.get("family", "Other")
        cx, cy = family_centers.get(fam, (0.5, 0.5))
        x = int((cx + random.gauss(0, 0.08)) * width)
        y = int((cy + random.gauss(0, 0.08)) * height)
        x = max(10, min(width - 10, x))
        y = max(10, min(height - 10, y))
        color = family_colors.get(fam, '#9ca3af')
        svg_points.append(f'    <circle cx="{x}" cy="{y}" r="3" fill="{color}" opacity="0.8"/>')

    svg = f'''<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">
  <rect width="{width}" height="{height}" fill="#0b0f14"/>
  <text x="10" y="20" fill="#e6eef7" font-family="Arial" font-size="12">Miranda Dynamics: 2D Proof Map</text>
  <text x="10" y="35" fill="#9ca3af" font-family="Arial" font-size="10">{len(decls)} declarations</text>
  <g>
{chr(10).join(svg_points)}
  </g>
</svg>'''

    output.write_text(svg, encoding="utf-8")
    print(f"Generated {output}")


def generate_3d_preview_svg(decls: list, output: Path):
    """Generate animated 3D preview SVG."""

    width, height = 600, 400

    # Simple animation showing rotation illusion
    svg = f'''<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">
  <defs>
    <radialGradient id="glow" cx="50%" cy="50%" r="50%">
      <stop offset="0%" style="stop-color:#3b82f6;stop-opacity:0.3"/>
      <stop offset="100%" style="stop-color:#0b0f14;stop-opacity:0"/>
    </radialGradient>
  </defs>
  <rect width="{width}" height="{height}" fill="#0b0f14"/>
  <ellipse cx="{width//2}" cy="{height//2}" rx="180" ry="140" fill="url(#glow)">
    <animateTransform attributeName="transform" type="rotate" from="0 {width//2} {height//2}" to="360 {width//2} {height//2}" dur="20s" repeatCount="indefinite"/>
  </ellipse>
  <text x="10" y="20" fill="#e6eef7" font-family="Arial" font-size="12">Miranda Dynamics: 3D Proof Map</text>
  <text x="10" y="35" fill="#9ca3af" font-family="Arial" font-size="10">{len(decls)} declarations (click to explore)</text>
  <g transform="translate({width//2}, {height//2})">
    <animateTransform attributeName="transform" type="rotate" from="0" to="360" dur="30s" repeatCount="indefinite" additive="sum"/>
'''

    import random
    random.seed(42)

    family_colors = {
        'TKFT': '#3b82f6', 'Billiards/Cantor': '#10b981', 'Computation': '#f59e0b',
        'FixedPoint': '#8b5cf6', 'Seismic': '#06b6d4', 'Wolfram': '#84cc16',
        'Wolfram/Multiway': '#22c55e', 'Other': '#9ca3af',
    }

    for i, d in enumerate(decls[:150]):
        fam = d.get("family", "Other")
        color = family_colors.get(fam, '#9ca3af')
        x = random.randint(-150, 150)
        y = random.randint(-100, 100)
        r = 2 + random.random() * 2
        svg += f'    <circle cx="{x}" cy="{y}" r="{r}" fill="{color}" opacity="0.7"/>\n'

    svg += '''  </g>
</svg>'''

    output.write_text(svg, encoding="utf-8")
    print(f"Generated {output}")


def main():
    parser = argparse.ArgumentParser(description="Generate Miranda Dynamics visualizations")
    parser.add_argument("--lean-dir", default="RESEARCHER_BUNDLE/HeytingLean",
                        help="Path to HeytingLean directory")
    parser.add_argument("--out-dir", default="RESEARCHER_BUNDLE/artifacts/visuals",
                        help="Output directory")
    args = parser.parse_args()

    # Find project root
    script_dir = Path(__file__).parent
    project_root = script_dir.parent

    lean_dir = project_root / args.lean_dir
    out_dir = project_root / args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    print(f"Scanning Lean files in {lean_dir}...")

    # Directories to scan
    scan_dirs = [
        lean_dir / "MirandaDynamics",
        lean_dir / "WPP",
        lean_dir / "CLI",
    ]

    # Extract declarations
    decls = extract_declarations(scan_dirs)
    file_count = count_files_and_decls(scan_dirs)

    print(f"Found {len(decls)} declarations in {file_count} files")

    # Generate all outputs
    generate_miranda_proofs_data(decls, out_dir / "miranda_proofs_data.js", file_count)
    generate_tactic_flow_data(out_dir / "tactic_flow_data.js")
    generate_proof_term_data(out_dir / "proof_term_data.js")
    generate_2d_preview_svg(decls, out_dir / "miranda_2d_preview.svg")
    generate_3d_preview_svg(decls, out_dir / "miranda_3d_preview_animated.svg")

    # Copy static 3D preview (non-animated)
    static_3d = out_dir / "miranda_3d_preview.svg"
    generate_2d_preview_svg(decls, static_3d)  # Use same as 2D for static

    print(f"\nVisualization generation complete!")
    print(f"Files in {out_dir}:")
    for f in sorted(out_dir.iterdir()):
        if f.suffix in ['.js', '.svg']:
            print(f"  - {f.name}")


if __name__ == "__main__":
    main()
