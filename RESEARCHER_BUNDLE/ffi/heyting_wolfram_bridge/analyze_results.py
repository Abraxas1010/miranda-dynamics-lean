#!/usr/bin/env python3
"""
Comprehensive analysis of Wolfram Physics hypergraph evolution results.
Generates statistics, visualizations, and structural insights.
"""

import json
import struct
import os
import sys
from collections import defaultdict
from typing import List, Tuple, Dict
import math


def load_hypergraph(model_dir: str, model_name: str) -> Tuple[List[Tuple[int, ...]], dict]:
    """Load hypergraph from binary files."""
    meta_path = os.path.join(model_dir, f"{model_name}_metadata.json")
    data_path = os.path.join(model_dir, f"{model_name}_hypergraph.bin")
    lengths_path = os.path.join(model_dir, f"{model_name}_lengths.bin")

    with open(meta_path) as f:
        metadata = json.load(f)

    count = metadata['finalStateSize']

    # Load lengths
    lengths = []
    with open(lengths_path, 'rb') as f:
        for _ in range(count):
            lengths.append(struct.unpack('<q', f.read(8))[0])

    # Load data
    total_len = sum(lengths)
    data = []
    with open(data_path, 'rb') as f:
        for _ in range(total_len):
            data.append(struct.unpack('<q', f.read(8))[0])

    # Reconstruct edges
    edges = []
    offset = 0
    for length in lengths:
        edge = tuple(data[offset:offset + length])
        edges.append(edge)
        offset += length

    return edges, metadata


def compute_degree_distribution(edges: List[Tuple[int, ...]]) -> Dict[int, int]:
    """Compute vertex degree distribution."""
    degree_count = defaultdict(int)
    for edge in edges:
        for v in edge:
            degree_count[v] += 1

    # Convert to histogram: degree -> count
    histogram = defaultdict(int)
    for v, deg in degree_count.items():
        histogram[deg] += 1

    return dict(histogram)


def compute_edge_arity_distribution(edges: List[Tuple[int, ...]]) -> Dict[int, int]:
    """Compute distribution of edge sizes (arities)."""
    arity_count = defaultdict(int)
    for edge in edges:
        arity_count[len(edge)] += 1
    return dict(arity_count)


def compute_clustering_coefficient(edges: List[Tuple[int, ...]]) -> float:
    """
    Compute a generalized clustering coefficient for hypergraphs.
    Based on the ratio of closed triangles to potential triangles.
    """
    # Build adjacency (for 2-edges only)
    if all(len(e) == 2 for e in edges):
        neighbors = defaultdict(set)
        for e in edges:
            neighbors[e[0]].add(e[1])
            neighbors[e[1]].add(e[0])

        triangles = 0
        triples = 0

        for v in neighbors:
            neighs = list(neighbors[v])
            n = len(neighs)
            if n < 2:
                continue
            triples += n * (n - 1) // 2
            for i in range(n):
                for j in range(i + 1, n):
                    if neighs[j] in neighbors[neighs[i]]:
                        triangles += 1

        if triples == 0:
            return 0.0
        return triangles / triples

    # For hypergraphs, use a simplified measure
    return -1.0  # Not computed for non-2-uniform hypergraphs


def compute_diameter_estimate(edges: List[Tuple[int, ...]]) -> int:
    """Estimate graph diameter using BFS from random vertices."""
    if not all(len(e) == 2 for e in edges):
        return -1  # Only for 2-uniform

    # Build adjacency
    neighbors = defaultdict(set)
    for e in edges:
        neighbors[e[0]].add(e[1])
        neighbors[e[1]].add(e[0])

    if not neighbors:
        return 0

    vertices = list(neighbors.keys())

    # BFS from first vertex
    start = vertices[0]
    visited = {start}
    frontier = [start]
    diameter = 0

    while frontier:
        next_frontier = []
        for v in frontier:
            for n in neighbors[v]:
                if n not in visited:
                    visited.add(n)
                    next_frontier.append(n)
        if next_frontier:
            diameter += 1
        frontier = next_frontier

    return diameter


def analyze_model(model_dir: str, model_name: str) -> dict:
    """Full analysis of a single model."""
    edges, metadata = load_hypergraph(model_dir, model_name)

    # Basic stats
    vertices = set()
    for e in edges:
        vertices.update(e)

    vertex_degrees = defaultdict(int)
    for e in edges:
        for v in e:
            vertex_degrees[v] += 1

    degrees = list(vertex_degrees.values())

    analysis = {
        'model': model_name,
        'metadata': metadata,
        'basic': {
            'edge_count': len(edges),
            'vertex_count': len(vertices),
            'total_incidences': sum(len(e) for e in edges),
        },
        'degree': {
            'min': min(degrees) if degrees else 0,
            'max': max(degrees) if degrees else 0,
            'mean': sum(degrees) / len(degrees) if degrees else 0,
            'distribution': compute_degree_distribution(edges),
        },
        'arity': {
            'distribution': compute_edge_arity_distribution(edges),
            'uniform': len(set(len(e) for e in edges)) == 1,
        },
        'topology': {
            'clustering_coefficient': compute_clustering_coefficient(edges),
            'diameter_estimate': compute_diameter_estimate(edges),
        }
    }

    # Growth metrics
    if 'eventCount' in metadata:
        analysis['growth'] = {
            'events': metadata['eventCount'],
            'edges_per_event': len(edges) / metadata['eventCount'] if metadata['eventCount'] > 0 else 0,
            'vertices_per_event': len(vertices) / metadata['eventCount'] if metadata['eventCount'] > 0 else 0,
        }

    return analysis


def print_analysis(analysis: dict):
    """Pretty print analysis results."""
    print(f"\n{'='*70}")
    print(f" MODEL: {analysis['model'].upper()}")
    print(f"{'='*70}")

    b = analysis['basic']
    print(f"\nBASIC STATISTICS:")
    print(f"  Edges: {b['edge_count']}")
    print(f"  Vertices: {b['vertex_count']}")
    print(f"  Total incidences: {b['total_incidences']}")
    print(f"  Edge density: {b['edge_count'] / max(1, b['vertex_count']):.3f} edges/vertex")

    d = analysis['degree']
    print(f"\nDEGREE DISTRIBUTION:")
    print(f"  Min degree: {d['min']}")
    print(f"  Max degree: {d['max']}")
    print(f"  Mean degree: {d['mean']:.2f}")
    print(f"  Distribution: ", end="")
    dist = sorted(d['distribution'].items())
    if len(dist) <= 10:
        print(", ".join(f"d={deg}: {cnt}" for deg, cnt in dist))
    else:
        print(f"{len(dist)} distinct values")

    a = analysis['arity']
    print(f"\nEDGE ARITY:")
    print(f"  Uniform: {a['uniform']}")
    print(f"  Distribution: {a['distribution']}")

    t = analysis['topology']
    print(f"\nTOPOLOGICAL PROPERTIES:")
    if t['clustering_coefficient'] >= 0:
        print(f"  Clustering coefficient: {t['clustering_coefficient']:.4f}")
    else:
        print(f"  Clustering coefficient: N/A (non-2-uniform)")

    if t['diameter_estimate'] >= 0:
        print(f"  Diameter estimate: {t['diameter_estimate']}")
    else:
        print(f"  Diameter estimate: N/A (non-2-uniform)")

    if 'growth' in analysis:
        g = analysis['growth']
        print(f"\nGROWTH METRICS:")
        print(f"  Total events: {g['events']}")
        print(f"  Final edges / events: {g['edges_per_event']:.2f}")
        print(f"  Final vertices / events: {g['vertices_per_event']:.2f}")


def comparative_analysis(results: List[dict]):
    """Compare all models."""
    print("\n" + "="*70)
    print(" COMPARATIVE ANALYSIS")
    print("="*70)

    print("\n{:<18} {:>8} {:>8} {:>8} {:>8} {:>8}".format(
        "Model", "Edges", "Verts", "MaxDeg", "Cluster", "Diameter"
    ))
    print("-"*70)

    for r in results:
        cc = r['topology']['clustering_coefficient']
        dia = r['topology']['diameter_estimate']
        print("{:<18} {:>8} {:>8} {:>8} {:>8} {:>8}".format(
            r['model'],
            r['basic']['edge_count'],
            r['basic']['vertex_count'],
            r['degree']['max'],
            f"{cc:.3f}" if cc >= 0 else "N/A",
            dia if dia >= 0 else "N/A"
        ))

    # Insights
    print("\nINSIGHTS:")

    # Find most connected
    most_connected = max(results, key=lambda r: r['degree']['max'])
    print(f"  - Most connected: {most_connected['model']} (max degree {most_connected['degree']['max']})")

    # Find highest clustering
    clustered = [r for r in results if r['topology']['clustering_coefficient'] >= 0]
    if clustered:
        best_cluster = max(clustered, key=lambda r: r['topology']['clustering_coefficient'])
        print(f"  - Highest clustering: {best_cluster['model']} ({best_cluster['topology']['clustering_coefficient']:.4f})")

    # Find largest diameter
    with_diameter = [r for r in results if r['topology']['diameter_estimate'] >= 0]
    if with_diameter:
        largest_dia = max(with_diameter, key=lambda r: r['topology']['diameter_estimate'])
        print(f"  - Largest diameter: {largest_dia['model']} ({largest_dia['topology']['diameter_estimate']})")

    # Growth efficiency
    print("\nGROWTH EFFICIENCY (final edges per event):")
    for r in sorted(results, key=lambda r: r.get('growth', {}).get('edges_per_event', 0), reverse=True):
        if 'growth' in r:
            print(f"  {r['model']}: {r['growth']['edges_per_event']:.2f}")


def main():
    output_base = os.environ.get('HYPERGRAPH_OUTPUT_BASE', '/tmp/hypergraph_analysis_py')
    models = ['universe1', 'stringTheory', 'triangleGrowth', 'starExpansion', 'minimalCausal']

    results = []

    for model in models:
        model_dir = os.path.join(output_base, model)
        if os.path.exists(model_dir):
            try:
                analysis = analyze_model(model_dir, model)
                print_analysis(analysis)
                results.append(analysis)
            except Exception as e:
                print(f"Error analyzing {model}: {e}")

    if len(results) > 1:
        comparative_analysis(results)

    # Save full results
    output_path = os.path.join(output_base, 'full_analysis.json')
    with open(output_path, 'w') as f:
        # Convert non-serializable items
        def clean(obj):
            if isinstance(obj, dict):
                return {k: clean(v) for k, v in obj.items()}
            elif isinstance(obj, list):
                return [clean(v) for v in obj]
            elif isinstance(obj, (int, float, str, bool, type(None))):
                return obj
            else:
                return str(obj)

        json.dump(clean(results), f, indent=2)

    print(f"\nFull analysis saved to: {output_path}")


if __name__ == '__main__':
    main()
