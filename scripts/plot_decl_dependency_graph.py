#!/usr/bin/env python3

"""Render an undirected declaration dependency graph with Graphviz.

Nodes are declarations from the cached `decl-frequencies` data. An undirected
edge is drawn between declarations when one depends on the other. Each
declaration's radial distance from the center is derived from its
`relative_frequency` in the dependency-frequency dataframe: more common
dependencies are placed closer to the center, rarer ones farther out.
"""

from __future__ import annotations

import argparse
from pathlib import Path
from typing import TYPE_CHECKING

from decl_frequencies_dataframe import (
    DEFAULT_EXCLUDE_ROOTS,
    build_dependency_index,
    get_decl_frequencies_dataframe,
)

if TYPE_CHECKING:
    import pandas as pd
    import graphviz


def require_graphviz():
    try:
        import graphviz
    except ModuleNotFoundError as exc:
        raise SystemExit(
            "The Python `graphviz` package is required. Install it with "
            "`python3 -m pip install graphviz`, and ensure the Graphviz "
            "system binaries are on PATH."
        ) from exc
    return graphviz


def declaration_relative_frequency_map(df: "pd.DataFrame") -> dict[str, float]:
    return {
        str(dependency): float(relative_frequency)
        for dependency, relative_frequency in zip(
            df["dependency"],
            df["relative_frequency"],
            strict=True,
        )
    }


def compute_radii(
    declarations: list[str],
    relative_frequency_map: dict[str, float],
    min_radius: float,
    max_radius: float,
) -> dict[str, float]:
    import math

    positive_values = sorted(
        rf for decl, rf in relative_frequency_map.items() if decl in declarations and rf > 0
    )
    if not positive_values:
        midpoint = (min_radius + max_radius) / 2.0
        return {decl: midpoint for decl in declarations}

    min_positive = positive_values[0]
    max_positive = positive_values[-1]
    log_min = math.log(min_positive)
    log_max = math.log(max_positive)

    radii: dict[str, float] = {}
    for decl in declarations:
        rf = relative_frequency_map.get(decl, 0.0)
        if rf <= 0:
            radii[decl] = max_radius
            continue
        if math.isclose(log_min, log_max):
            normalized = 0.0
        else:
            normalized = (log_max - math.log(rf)) / (log_max - log_min)
        radii[decl] = min_radius + normalized * (max_radius - min_radius)
    return radii


def compute_positions(
    declarations: list[str],
    radii: dict[str, float],
    position_scale: float,
    namespace_depth: int,
) -> dict[str, tuple[float, float]]:
    import math

    def namespace_key(decl: str) -> tuple[tuple[str, ...], str]:
        parts = tuple(decl.split("."))
        prefix = parts[:namespace_depth] if namespace_depth > 0 else ()
        return (prefix, decl)

    ordered = sorted(declarations, key=namespace_key)
    if not ordered:
        return {}

    positions: dict[str, tuple[float, float]] = {}
    total = len(ordered)
    for index, decl in enumerate(ordered):
        radius = radii[decl] * position_scale
        angle = (2.0 * math.pi * index) / total
        x = radius * math.cos(angle)
        y = radius * math.sin(angle)
        positions[decl] = (x, y)
    return positions


def build_edges(
    dependency_index: dict[str, list[str]],
    declarations: set[str],
) -> set[tuple[str, str]]:
    edges: set[tuple[str, str]] = set()
    for declaration, dependencies in dependency_index.items():
        if declaration not in declarations:
            continue
        for dependency in dependencies:
            if dependency not in declarations or dependency == declaration:
                continue
            edge = tuple(sorted((declaration, dependency)))
            edges.add(edge)
    return edges


def render_graph(
    declarations: list[str],
    dependency_index: dict[str, list[str]],
    relative_frequency_map: dict[str, float],
    output_path: Path,
    output_format: str,
    min_radius: float,
    max_radius: float,
    position_scale: float,
    namespace_depth: int,
    node_size: float,
    edge_penwidth: float,
    show_labels: bool,
    label_fontsize: float,
    root_name: str = "__root__",
) -> Path:
    graphviz = require_graphviz()
    radii = compute_radii(declarations, relative_frequency_map, min_radius, max_radius)
    positions = compute_positions(declarations, radii, position_scale, namespace_depth)
    declaration_set = set(declarations)
    edges = build_edges(dependency_index, declaration_set)

    graph = graphviz.Graph(
        name="decl_dependency_graph",
        engine="neato",
        format=output_format,
        strict=True,
        graph_attr={
            "overlap": "false",
            "splines": "true",
            "outputorder": "edgesfirst",
            "notranslate": "true",
            "sep": "+8",
            "pad": "0.5",
            "start": "regular",
        },
        node_attr={
            "shape": "point",
            "width": f"{node_size}",
            "height": f"{node_size}",
            "fixedsize": "true",
            "pin": "true",
            "label": "",
            "xlabel": "",
            "style": "filled",
            "fillcolor": "#1f77b4",
            "color": "#1f77b4",
        },
        edge_attr={
            "color": "#99999955",
            "penwidth": f"{edge_penwidth}",
        },
    )

    graph.node(
        root_name,
        pos="0,0!",
        width="0.03",
        height="0.03",
        fillcolor="#d62728",
        color="#d62728",
        xlabel="root",
    )

    for declaration in declarations:
        x, y = positions[declaration]
        rf = relative_frequency_map.get(declaration, 0.0)
        graph.node(
            declaration,
            pos=f"{x:.6f},{y:.6f}!",
            xlabel=declaration if show_labels else "",
            fontsize=f"{label_fontsize}",
            tooltip=f"{declaration} | relative_frequency={rf:.8e}",
        )

    for left, right in sorted(edges):
        graph.edge(left, right)

    if declarations:
        graph.edge(root_name, declarations[0], style="invis")

    output_path.parent.mkdir(parents=True, exist_ok=True)
    rendered = graph.render(
        filename=output_path.stem,
        directory=str(output_path.parent),
        cleanup=False,
        neato_no_op=2,
    )
    return Path(rendered)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Render an undirected declaration dependency graph using the cached "
            "`decl-frequencies` data and position nodes radially by "
            "relative frequency."
        )
    )
    parser.add_argument("--project", default="Mathlib")
    parser.add_argument("--exclude-roots", default=DEFAULT_EXCLUDE_ROOTS)
    parser.add_argument("--include-private", action="store_true")
    parser.add_argument("--cache-dir", type=Path, default=Path("out/decl_frequencies"))
    parser.add_argument("--force-cache", action="store_true")
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("out/decl_frequencies/decl_dependency_graph"),
        help="Output path without extension or with a matching extension.",
    )
    parser.add_argument("--format", default="svg")
    parser.add_argument("--min-radius", type=float, default=2.0)
    parser.add_argument("--max-radius", type=float, default=40.0)
    parser.add_argument(
        "--position-scale",
        type=float,
        default=120.0,
        help="Multiplier applied to computed positions before rendering.",
    )
    parser.add_argument(
        "--namespace-depth",
        type=int,
        default=1,
        help=(
            "Group angular ordering by the first N namespace components so "
            "related declarations occupy nearby slices."
        ),
    )
    parser.add_argument("--node-size", type=float, default=0.4)
    parser.add_argument("--edge-penwidth", type=float, default=4)
    parser.add_argument(
        "--show-labels",
        action="store_true",
        help="Render declaration names as small labels next to nodes.",
    )
    parser.add_argument(
        "--label-fontsize",
        type=float,
        default=6.0,
        help="Font size for declaration labels when --show-labels is set.",
    )
    parser.add_argument(
        "--limit",
        type=int,
        default=None,
        help="Optional cap on number of declarations rendered, for debugging.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    repo_root = Path(__file__).resolve().parents[1]
    cache_dir = args.cache_dir
    if not cache_dir.is_absolute():
        cache_dir = repo_root / cache_dir

    df, records = get_decl_frequencies_dataframe(
        project=args.project,
        exclude_roots=args.exclude_roots,
        include_private=args.include_private,
        cache_dir=cache_dir,
        repo_root=repo_root,
        force=args.force_cache,
    )
    dependency_index = build_dependency_index(records)
    declarations = sorted(dependency_index)
    if args.limit is not None:
        declarations = declarations[: args.limit]

    relative_frequency_map = declaration_relative_frequency_map(df)

    output = args.output
    if not output.is_absolute():
        output = repo_root / output
    if output.suffix == f".{args.format}":
        output = output.with_suffix("")

    rendered_path = render_graph(
        declarations=declarations,
        dependency_index=dependency_index,
        relative_frequency_map=relative_frequency_map,
        output_path=output,
        output_format=args.format,
        min_radius=args.min_radius,
        max_radius=args.max_radius,
        position_scale=args.position_scale,
        namespace_depth=args.namespace_depth,
        node_size=args.node_size,
        edge_penwidth=args.edge_penwidth,
        show_labels=args.show_labels,
        label_fontsize=args.label_fontsize,
    )

    print(f"Rendered {len(declarations)} declarations to {rendered_path}")


if __name__ == "__main__":
    main()
