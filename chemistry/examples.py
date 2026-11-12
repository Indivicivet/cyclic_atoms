"""Write exact examples, reaction paths, the complete weight table, and graph plots.

Usage from the repository root: python -m chemistry.examples [--outdir DIR]
"""

import argparse
import csv
import json
from itertools import product
from pathlib import Path

import networkx as nx

import chemistry.model as model
import chemistry.plots as plots
import visualization.core as core


def weight_table():
    """One of each complementary pair of 3–5–7 bit-weight profiles.

    Coordinate permutations preserve the bond graph but need not be rotations.
    Consequently these rows classify graphs/formulas for this computation, not
    molecules up to the project's geometric equivalence.
    """
    rows = []
    for a, b, c in product(range(2), range(6), range(8)):
        atoms = model.weight_configuration((3, 5, 7), (a, b, c))
        _, graph = model.inspect_open(atoms)
        counts = model.formula(atoms)
        batch, recipe = model.batch_recipe(counts)
        rows.append(
            {
                "a": a,
                "b": b,
                "c": c,
                "n3": counts.get(3, 0),
                "n5": counts.get(5, 0),
                "n7": counts.get(7, 0),
                "atoms": len(atoms),
                "components": nx.number_connected_components(graph),
                "connected_three_element": len(counts) == 3 and nx.is_connected(graph),
                "bipartite": nx.is_bipartite(graph),
                "minimum_batch": batch,
                "M35": recipe[(3, 5)],
                "M37": recipe[(3, 7)],
                "M57": recipe[(5, 7)],
            }
        )
    return rows


def write_atoms(path, atoms):
    path.write_text(
        json.dumps([[p, str(phase)] for p, phase, _ in atoms], indent=2) + "\n",
        encoding="utf-8",
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--outdir", type=Path, default=Path(__file__).parent / "output")
    args = parser.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    maximum = model.weight_configuration((3, 5, 7), (1, 0, 7))
    mixed = model.weight_configuration((3, 5, 7), (1, 1, 1))
    fusion = model.binary_fusion(3, 5, 7)
    for name, atoms in (
        ("maximum_357", maximum),
        ("mixed_357", mixed),
        ("fusion_357", fusion["product"]),
    ):
        core.analyze(atoms)
        write_atoms(args.outdir / f"{name}.json", atoms)
    path = model.atomization_path(
        (maximum,) * 3,
        (model.binary_molecule(3, 5),) * 14 + (model.binary_molecule(3, 7),) * 5,
    )
    (args.outdir / "batch_path.json").write_text(
        json.dumps(path, default=str, indent=2) + "\n", encoding="utf-8"
    )
    rows = weight_table()
    with (args.outdir / "weight_profiles.csv").open(
        "w", newline="", encoding="utf-8"
    ) as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    plots.maximum_graph(maximum, args.outdir)
    plots.fusion_graph(fusion, args.outdir)
    plots.batch_split(maximum, args.outdir)
    plots.mixed_graph(mixed, args.outdir)
    connected = [row for row in rows if row["connected_three_element"]]
    print(
        "Wrote 4 graph figures (PNG + SVG), exact molecules, "
        f"and a 324-move path to {args.outdir}"
    )
    print(
        f"Checked {len(rows)} weight profiles; {len(connected)} are connected "
        "and use all three elements."
    )
    print(
        "Single-copy binary decompositions:",
        sum(row["minimum_batch"] == 1 for row in connected),
    )


if __name__ == "__main__":
    main()
