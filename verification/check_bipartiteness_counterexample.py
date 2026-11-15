"""Construct and exactly verify the four-prime non-bipartite molecule.

Run from the repository root with
``python -m verification.check_bipartiteness_counterexample``.
"""

import json
from collections import Counter
from fractions import Fraction
from itertools import product
from pathlib import Path

import networkx as nx

import visualization.core as core

ELEMENTS = (3, 5, 7, 2)
GRID_SIZE = 210
# Each None is the coordinate varying along that atom. The order is a 7-cycle.
BASE_LINES = (
    (None, 0, 0),
    (1, None, 0),
    (None, 1, 0),
    (2, 1, None),
    (None, 1, 1),
    (0, None, 1),
    (0, 0, None),
)


def base_points(line):
    return tuple(
        product(*(range(p) if x is None else (x,) for p, x in zip(ELEMENTS, line)))
    )


def circle_index(point):
    # CRT idempotents send (x, y, z, t) to an integer with those residues.
    return sum(w * x for w, x in zip((70, 126, 120, 105), point)) % GRID_SIZE


def construct():
    base_occupancy = Counter(
        point for line in BASE_LINES for point in base_points(line)
    )
    assert Counter(base_occupancy.values()) == {1: 19, 2: 7}
    lines = tuple((*line, layer) for layer in range(2) for line in BASE_LINES) + tuple(
        (*point, None) for point, count in sorted(base_occupancy.items()) if count == 1
    )
    return tuple(
        (
            ELEMENTS[line.index(None)],
            Fraction(
                circle_index(tuple(0 if x is None else x for x in line)), GRID_SIZE
            )
            % Fraction(1, ELEMENTS[line.index(None)]),
            None,
        )
        for line in lines
    )


def main():
    atoms = construct()
    occupancy, graph = core.analyze(atoms)
    assert len(atoms) == 33
    assert Counter(p for p, _, _ in atoms) == {2: 19, 3: 6, 5: 4, 7: 4}
    assert len(occupancy) == graph.number_of_edges() == 52
    assert all(len(owners) == 2 for owners in occupancy.values())
    assert nx.is_connected(graph)
    assert not nx.is_bipartite(graph)
    assert all(graph.has_edge(i, (i + 1) % 7) for i in range(7))
    assert graph.subgraph(range(7)).number_of_edges() == 7
    assert all(graph.degree(i) == atom[0] for i, atom in enumerate(atoms))

    output = Path(__file__).with_name("nonbipartite_2357.json")
    output.write_text(
        json.dumps([[p, str(phase)] for p, phase, _ in atoms], indent=2) + "\n",
        encoding="utf-8",
    )
    # Re-read the exported circle phases, so the reusable artifact is checked too.
    _, exported_graph = core.analyze(core.read_atoms(output))
    assert not nx.is_bipartite(exported_graph)
    print("Verified 33 atoms, 52 bonds, exact occupancy 2, and a 7-cycle.")
    print("Formula: 2_19 3_6 5_4 7_4")
    print(f"Exact circle phases: {output}")
    print("Cycle atom indices: 0, 1, 2, 3, 4, 5, 6, 0")
    print(
        "Cycle bond phases:",
        ", ".join(str(graph.edges[i, (i + 1) % 7, 0]["phase"]) for i in range(7)),
    )


if __name__ == "__main__":
    main()
