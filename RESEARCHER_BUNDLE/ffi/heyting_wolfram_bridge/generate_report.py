#!/usr/bin/env python3
"""
Generate comprehensive report with ASCII visualizations for Wolfram Physics experiments.
"""

import json
import os
import sys
from datetime import datetime

def ascii_histogram(data: dict, title: str, width: int = 40) -> str:
    """Generate ASCII histogram."""
    if not data:
        return f"{title}\n  (no data)"

    lines = [title]
    max_val = max(data.values())

    for key in sorted(data.keys()):
        val = data[key]
        bar_len = int((val / max_val) * width) if max_val > 0 else 0
        bar = '█' * bar_len
        lines.append(f"  {key:>3}: {bar} {val}")

    return '\n'.join(lines)


def ascii_bar_chart(items: list, title: str, width: int = 40) -> str:
    """Generate ASCII bar chart from [(label, value), ...]."""
    if not items:
        return f"{title}\n  (no data)"

    lines = [title]
    max_val = max(v for _, v in items)
    max_label = max(len(str(l)) for l, _ in items)

    for label, val in items:
        bar_len = int((val / max_val) * width) if max_val > 0 else 0
        bar = '█' * bar_len
        lines.append(f"  {str(label):<{max_label}}: {bar} {val:.2f}")

    return '\n'.join(lines)


def generate_report(analysis_path: str, output_path: str):
    """Generate full markdown report."""

    with open(analysis_path) as f:
        results = json.load(f)

    backend = "unknown"
    if results:
        meta0 = results[0].get("metadata", {})
        if isinstance(meta0, dict) and "steps" in meta0:
            backend = "wolfram"
        elif isinstance(meta0, dict) and "totalDataLength" in meta0:
            backend = "python"

    report = []
    report.append("# Wolfram Physics Hypergraph Analysis Report")
    report.append(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    report.append(f"Backend: {backend}")
    report.append("")
    report.append("## Executive Summary")
    report.append("")
    report.append("This report analyzes the evolution of 5 different Wolfram Physics hypergraph models,")
    report.append("examining their structural properties, growth dynamics, and topological characteristics.")
    report.append("")

    # Summary table
    report.append("### Model Comparison")
    report.append("")
    report.append("| Model | Edges | Vertices | Max Degree | Clustering | Diameter |")
    report.append("|-------|-------|----------|------------|------------|----------|")

    for r in results:
        cc = r['topology']['clustering_coefficient']
        dia = r['topology']['diameter_estimate']
        cc_str = f"{cc:.3f}" if cc >= 0 else "N/A"
        dia_str = str(dia) if dia >= 0 else "N/A"
        report.append(f"| {r['model']} | {r['basic']['edge_count']} | {r['basic']['vertex_count']} | {r['degree']['max']} | {cc_str} | {dia_str} |")

    report.append("")

    # Insights
    report.append("### Key Insights")
    report.append("")

    # Find extremes
    most_edges = max(results, key=lambda r: r['basic']['edge_count'])
    most_vertices = max(results, key=lambda r: r['basic']['vertex_count'])
    most_connected = max(results, key=lambda r: r['degree']['max'])

    report.append(f"1. **Most prolific edge generation**: {most_edges['model']} ({most_edges['basic']['edge_count']} edges)")
    report.append(f"2. **Most vertex generation**: {most_vertices['model']} ({most_vertices['basic']['vertex_count']} vertices)")
    report.append(f"3. **Most highly connected**: {most_connected['model']} (max degree {most_connected['degree']['max']})")

    # Clustering insight
    clustered = [r for r in results if r['topology']['clustering_coefficient'] > 0]
    if clustered:
        best_cluster = max(clustered, key=lambda r: r['topology']['clustering_coefficient'])
        report.append(f"4. **Highest clustering coefficient**: {best_cluster['model']} ({best_cluster['topology']['clustering_coefficient']:.4f})")
        report.append("   - Indicates more triangle-like local structure")

    report.append("")

    # Detailed model analysis
    report.append("## Detailed Model Analysis")
    report.append("")

    for r in results:
        report.append(f"### {r['model']}")
        report.append("")

        # Basic stats
        report.append("**Basic Statistics:**")
        report.append(f"- Edge count: {r['basic']['edge_count']}")
        report.append(f"- Vertex count: {r['basic']['vertex_count']}")
        report.append(f"- Edge density: {r['basic']['edge_count'] / max(1, r['basic']['vertex_count']):.3f} edges/vertex")
        report.append("")

        # Degree distribution
        report.append("**Degree Distribution:**")
        report.append(f"- Min: {r['degree']['min']}, Max: {r['degree']['max']}, Mean: {r['degree']['mean']:.2f}")
        report.append("")
        report.append("```")
        dist = r['degree']['distribution']
        # Convert string keys to int for sorting
        dist_int = {int(k): v for k, v in dist.items()}
        report.append(ascii_histogram(dist_int, "Vertex Degree Histogram", 30))
        report.append("```")
        report.append("")

        # Edge arity
        arity = r['arity']['distribution']
        arity_int = {int(k): v for k, v in arity.items()}
        report.append(f"**Edge Arity:** {'Uniform' if r['arity']['uniform'] else 'Mixed'} - {arity_int}")
        report.append("")

        # Topology
        cc = r['topology']['clustering_coefficient']
        dia = r['topology']['diameter_estimate']
        report.append("**Topological Properties:**")
        if cc >= 0:
            report.append(f"- Clustering coefficient: {cc:.4f}")
            if cc > 0.3:
                report.append("  - High clustering indicates dense local neighborhoods")
            elif cc > 0.1:
                report.append("  - Moderate clustering suggests some triangular structures")
            else:
                report.append("  - Low/zero clustering indicates tree-like or linear structure")
        else:
            report.append("- Clustering coefficient: N/A (hypergraph with arity > 2)")

        if dia >= 0:
            report.append(f"- Diameter: {dia}")
            if dia <= 3:
                report.append("  - Small world property: any vertex reachable in few hops")
            elif dia > 20:
                report.append("  - Large diameter indicates elongated/chain-like structure")
        report.append("")

        # Growth
        if 'growth' in r:
            g = r['growth']
            report.append("**Growth Dynamics:**")
            report.append(f"- Events applied: {g['events']}")
            report.append(f"- Edge growth rate: {g['edges_per_event']:.2f} edges/event")
            report.append(f"- Vertex growth rate: {g['vertices_per_event']:.2f} vertices/event")
            report.append("")

    # Growth comparison chart
    report.append("## Growth Efficiency Comparison")
    report.append("")
    report.append("```")
    growth_data = [(r['model'], r['growth']['edges_per_event'])
                   for r in results if 'growth' in r]
    growth_data.sort(key=lambda x: x[1], reverse=True)
    report.append(ascii_bar_chart(growth_data, "Edges Generated per Rewriting Event", 35))
    report.append("```")
    report.append("")

    # Methodology
    report.append("## Methodology")
    report.append("")
    report.append("### Implementation")
    if backend == "wolfram":
        report.append("- Wolfram Engine + SetReplace` (WolframModel) for hypergraph evolution")
        report.append("- HeytingLean-exported verified C kernel used via ForeignFunctionLoad (metric computation)")
        report.append("- C library for efficient binary data analysis")
    elif backend == "python":
        report.append("- Pure Python hypergraph rewriting system (no Wolfram Engine dependency)")
        report.append("- C library for efficient binary data analysis")
        report.append("- Random match selection strategy for evolution")
    else:
        report.append("- Hypergraph evolution backend not detected")
        report.append("- C library for efficient binary data analysis")
    report.append("")
    report.append("### Models Tested")
    report.append("")
    report.append("| Model | Rule | Initial State |")
    report.append("|-------|------|---------------|")
    report.append("| universe1 | `{1,2,3},{2,4,5} → {5,v,1},{v,4,2},{4,5,3}` | 2 ternary edges |")
    report.append("| stringTheory | `{1,2},{2,3} → {1,2},{2,v},{v,3}` | 5-cycle |")
    report.append("| triangleGrowth | `{1,2},{2,3},{3,1} → {1,2},{2,v},{v,3},{3,1},{1,v}` | triangle |")
    report.append("| starExpansion | `{1,2},{1,3},{1,4} → {2,3},{2,4},{2,v},{3,v},{4,v}` | 4-star |")
    report.append("| minimalCausal | `{1,2},{2,3} → {1,2},{2,3},{3,v},{v,1}` | 2-path |")
    report.append("")

    # Conclusions
    report.append("## Conclusions")
    report.append("")
    report.append("1. **Universe1** produces true hypergraphs (ternary edges), while other models produce graphs.")
    report.append("2. **StringTheory** creates long chains with zero clustering - pure 1D structure.")
    report.append("3. **TriangleGrowth** and **StarExpansion** generate clustered structures with small diameter.")
    report.append("4. **MinimalCausal** creates hub-and-spoke patterns with very high max degree.")
    report.append("5. Growth efficiency varies significantly: 1.0x for linear growth vs 2.0x for branching rules.")
    report.append("")
    report.append("---")
    report.append("*Generated by HeytingLean Wolfram Physics Analysis Pipeline*")

    # Write report
    with open(output_path, 'w') as f:
        f.write('\n'.join(report))

    print(f"Report generated: {output_path}")
    return output_path


if __name__ == '__main__':
    output_base = os.environ.get('HYPERGRAPH_OUTPUT_BASE', '/tmp/hypergraph_analysis_py')
    analysis_path = os.path.join(output_base, 'full_analysis.json')
    output_path = os.path.join(output_base, 'ANALYSIS_REPORT.md')

    if os.path.exists(analysis_path):
        generate_report(analysis_path, output_path)

        # Print summary to stdout
        with open(output_path) as f:
            print(f.read())
    else:
        print(f"Error: {analysis_path} not found. Run analyze_results.py first.")
