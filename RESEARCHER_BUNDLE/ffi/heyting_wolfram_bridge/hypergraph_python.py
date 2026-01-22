#!/usr/bin/env python3
"""
Wolfram Physics Hypergraph Rewriting System
Pure Python implementation for HeytingLean integration

This implements hypergraph rewriting rules similar to the Wolfram Physics Project,
but without requiring Wolfram Engine.
"""

import struct
import json
import os
import sys
import time
from collections import defaultdict
from itertools import permutations
from typing import List, Tuple, Set, Dict, Optional
from dataclasses import dataclass, field


@dataclass
class HypergraphState:
    """Represents the state of a hypergraph during evolution."""
    edges: List[Tuple[int, ...]]
    next_vertex: int = 1
    events: List[dict] = field(default_factory=list)

    def vertex_count(self) -> int:
        """Count unique vertices."""
        vertices = set()
        for edge in self.edges:
            vertices.update(edge)
        return len(vertices)

    def edge_count(self) -> int:
        return len(self.edges)

    def copy(self) -> 'HypergraphState':
        return HypergraphState(
            edges=[tuple(e) for e in self.edges],
            next_vertex=self.next_vertex,
            events=list(self.events)
        )


class HypergraphRule:
    """A hypergraph rewriting rule."""

    def __init__(self, lhs: List[Tuple[int, ...]], rhs: List[Tuple[int, ...]]):
        """
        lhs: List of hyperedge patterns to match (using small integers as pattern variables)
        rhs: List of hyperedge patterns to produce (can introduce new vertices as negative numbers)
        """
        self.lhs = [tuple(e) for e in lhs]
        self.rhs = [tuple(e) for e in rhs]

        # Extract pattern variables from LHS
        self.pattern_vars = set()
        for edge in self.lhs:
            self.pattern_vars.update(edge)

        # Find new vertices introduced in RHS (negative numbers)
        self.new_vars = set()
        for edge in self.rhs:
            for v in edge:
                if v < 0:
                    self.new_vars.add(v)

    def __repr__(self):
        return f"{self.lhs} -> {self.rhs}"


class HypergraphRewriter:
    """Implements hypergraph rewriting with multiple evolution strategies."""

    def __init__(self, rule: HypergraphRule, initial_state: List[Tuple[int, ...]]):
        self.rule = rule
        self.state = HypergraphState(
            edges=[tuple(e) for e in initial_state],
            next_vertex=max(max(e) for e in initial_state) + 1 if initial_state else 1
        )

    def find_matches(self) -> List[Dict[int, int]]:
        """Find all ways to match the LHS pattern in the current state."""
        matches = []
        edges = self.state.edges
        lhs = self.rule.lhs

        if len(lhs) == 0:
            return []

        # For each permutation of edges that could match LHS
        if len(edges) < len(lhs):
            return []

        # Generate all ways to select len(lhs) edges from edges
        from itertools import combinations

        for edge_combo in combinations(range(len(edges)), len(lhs)):
            selected_edges = [edges[i] for i in edge_combo]

            # Try all permutations of selected edges against LHS patterns
            for perm in permutations(range(len(lhs))):
                binding = self._try_match(selected_edges, [lhs[i] for i in perm])
                if binding is not None:
                    binding['_matched_indices'] = edge_combo
                    matches.append(binding)

        return matches

    def _try_match(self, edges: List[Tuple[int, ...]], patterns: List[Tuple[int, ...]]) -> Optional[Dict[int, int]]:
        """Try to match edges against patterns, returning variable bindings or None."""
        if len(edges) != len(patterns):
            return None

        binding = {}

        for edge, pattern in zip(edges, patterns):
            if len(edge) != len(pattern):
                return None

            for actual, var in zip(edge, pattern):
                if var in binding:
                    if binding[var] != actual:
                        return None
                else:
                    binding[var] = actual

        return binding

    def apply_match(self, binding: Dict[int, int]) -> None:
        """Apply a single match to transform the hypergraph."""
        matched_indices = binding['_matched_indices']

        # Create new vertices for RHS new_vars
        new_vertex_map = {}
        for v in self.rule.new_vars:
            new_vertex_map[v] = self.state.next_vertex
            self.state.next_vertex += 1

        # Build full binding including new vertices
        full_binding = {**binding, **new_vertex_map}
        del full_binding['_matched_indices']

        # Remove matched edges
        new_edges = []
        for i, edge in enumerate(self.state.edges):
            if i not in matched_indices:
                new_edges.append(edge)

        # Add RHS edges with substitutions
        for pattern in self.rule.rhs:
            new_edge = tuple(full_binding[v] for v in pattern)
            new_edges.append(new_edge)

        # Record event
        self.state.events.append({
            'matched': [self.state.edges[i] for i in matched_indices],
            'produced': [tuple(full_binding[v] for v in p) for p in self.rule.rhs]
        })

        self.state.edges = new_edges

    def evolve(self, steps: int, strategy: str = 'random') -> None:
        """Evolve the hypergraph for a number of steps."""
        import random

        for step in range(steps):
            matches = self.find_matches()

            if not matches:
                print(f"  No more matches at step {step}")
                break

            if strategy == 'random':
                match = random.choice(matches)
            elif strategy == 'first':
                match = matches[0]
            elif strategy == 'all':
                # Apply all non-overlapping matches
                used_indices = set()
                for match in matches:
                    indices = set(match['_matched_indices'])
                    if not indices & used_indices:
                        self.apply_match(match)
                        used_indices.update(indices)
                continue
            else:
                match = matches[0]

            self.apply_match(match)

    def export_binary(self, output_dir: str, model_name: str) -> dict:
        """Export hypergraph to binary format for C consumption."""
        os.makedirs(output_dir, exist_ok=True)

        edges = self.state.edges

        # Flatten data
        flat_data = []
        lengths = []
        for edge in edges:
            flat_data.extend(edge)
            lengths.append(len(edge))

        # Write binary data
        data_path = os.path.join(output_dir, f"{model_name}_hypergraph.bin")
        with open(data_path, 'wb') as f:
            for v in flat_data:
                f.write(struct.pack('<q', v))  # int64_t little-endian

        # Write lengths
        lengths_path = os.path.join(output_dir, f"{model_name}_lengths.bin")
        with open(lengths_path, 'wb') as f:
            for l in lengths:
                f.write(struct.pack('<q', l))

        # Write metadata
        metadata = {
            'model': model_name,
            'finalStateSize': len(edges),
            'eventCount': len(self.state.events),
            'vertexCount': self.state.vertex_count(),
            'totalDataLength': len(flat_data)
        }

        meta_path = os.path.join(output_dir, f"{model_name}_metadata.json")
        with open(meta_path, 'w') as f:
            json.dump(metadata, f, indent=2)

        return metadata


# Model definitions matching our Wolfram script
MODELS = {
    'universe1': {
        'name': 'Universe 1 (Classic 2->3)',
        'rule': HypergraphRule(
            lhs=[(1, 2, 3), (2, 4, 5)],
            rhs=[(5, -1, 1), (-1, 4, 2), (4, 5, 3)]
        ),
        'init': [(1, 2, 3), (2, 4, 5)],
        'description': 'The original Wolfram Physics model'
    },
    'stringTheory': {
        'name': 'String Theory Analog',
        'rule': HypergraphRule(
            lhs=[(1, 2), (2, 3)],
            rhs=[(1, 2), (2, -1), (-1, 3)]
        ),
        'init': [(1, 2), (2, 3), (3, 4), (4, 5), (5, 1)],
        'description': 'Edge subdivision mimicking string worldsheets'
    },
    'triangleGrowth': {
        'name': 'Triangle Growth',
        'rule': HypergraphRule(
            lhs=[(1, 2), (2, 3), (3, 1)],
            rhs=[(1, 2), (2, -1), (-1, 3), (3, 1), (1, -1)]
        ),
        'init': [(1, 2), (2, 3), (3, 1)],
        'description': 'Triangular structure expansion'
    },
    'starExpansion': {
        'name': 'Star to Clique',
        'rule': HypergraphRule(
            lhs=[(1, 2), (1, 3), (1, 4)],
            rhs=[(2, 3), (2, 4), (2, -1), (3, -1), (4, -1)]
        ),
        'init': [(1, 2), (1, 3), (1, 4), (1, 5)],
        'description': 'Star graph transforms to clique'
    },
    'minimalCausal': {
        'name': 'Minimal Causal',
        'rule': HypergraphRule(
            lhs=[(1, 2), (2, 3)],
            rhs=[(1, 2), (2, 3), (3, -1), (-1, 1)]
        ),
        'init': [(1, 2), (2, 3)],
        'description': 'Minimal rule with non-trivial causal structure'
    }
}


def analyze_model(model_key: str, steps: int, output_dir: str) -> dict:
    """Run analysis on a single model."""
    if model_key not in MODELS:
        print(f"Unknown model: {model_key}")
        return None

    model = MODELS[model_key]
    print(f"\n{'='*60}")
    print(f"Analyzing: {model['name']}")
    print(f"Rule: {model['rule']}")
    print(f"Steps: {steps}")
    print(f"{'='*60}")

    # Create rewriter
    rewriter = HypergraphRewriter(model['rule'], model['init'])

    print(f"Initial state: {len(rewriter.state.edges)} edges, {rewriter.state.vertex_count()} vertices")

    # Time the evolution
    start_time = time.time()
    rewriter.evolve(steps, strategy='random')
    elapsed = time.time() - start_time

    print(f"\nResults after evolution:")
    print(f"  Final hyperedges: {rewriter.state.edge_count()}")
    print(f"  Total events: {len(rewriter.state.events)}")
    print(f"  Vertices: {rewriter.state.vertex_count()}")
    print(f"  Time: {elapsed:.3f}s")

    # Export
    model_output = os.path.join(output_dir, model_key)
    metadata = rewriter.export_binary(model_output, model_key)
    print(f"\nExported to: {model_output}/")

    # Add timing to metadata
    metadata['evolutionTime'] = elapsed
    metadata['steps'] = steps

    return metadata


def run_all_models(output_base: str = '/tmp/hypergraph_analysis_py'):
    """Run all models and generate analysis."""
    print("="*60)
    print("WOLFRAM PHYSICS HYPERGRAPH ANALYSIS (Python)")
    print("="*60)

    step_counts = {
        'universe1': 50,
        'stringTheory': 100,
        'triangleGrowth': 50,  # Reduced - this one grows fast
        'starExpansion': 30,   # Reduced - needs specific pattern
        'minimalCausal': 100
    }

    results = {}

    for model_key in MODELS:
        steps = step_counts.get(model_key, 50)
        result = analyze_model(model_key, steps, output_base)
        if result:
            results[model_key] = result

    # Summary
    print("\n" + "="*60)
    print("SUMMARY")
    print("="*60)
    print(f"{'Model':<20} {'Edges':<10} {'Vertices':<10} {'Events':<10} {'Time':<10}")
    print("-"*60)

    for model_key, meta in results.items():
        print(f"{model_key:<20} {meta['finalStateSize']:<10} {meta['vertexCount']:<10} {meta['eventCount']:<10} {meta['evolutionTime']:.3f}s")

    print("="*60)
    print(f"Output directory: {output_base}")

    return results


if __name__ == '__main__':
    import argparse

    parser = argparse.ArgumentParser(description='Wolfram Physics Hypergraph Analysis')
    parser.add_argument('model', nargs='?', default='all',
                        help='Model to run (universe1, stringTheory, etc.) or "all"')
    parser.add_argument('steps', nargs='?', type=int, default=50,
                        help='Number of evolution steps')
    parser.add_argument('--output', '-o', default='/tmp/hypergraph_analysis_py',
                        help='Output directory')

    args = parser.parse_args()

    if args.model == 'all':
        run_all_models(args.output)
    else:
        analyze_model(args.model, args.steps, args.output)
