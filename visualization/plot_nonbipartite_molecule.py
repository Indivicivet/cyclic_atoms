"""Draw exact circle sites of the non-bipartite molecule, not just its graph.

Run from the repository root:
python -m visualization.plot_nonbipartite_molecule [--outdir PATH]
"""

import argparse
from math import cos, pi, sin
from pathlib import Path

import matplotlib

matplotlib.use("Agg")

import matplotlib.patches as patches
import matplotlib.pyplot as plt
import networkx as nx
from matplotlib.lines import Line2D

import verification.check_bipartiteness_counterexample as counterexample
import visualization.core as core

COLORS = {2: "#8995a1", 3: "#8b57b5", 5: "#d59023", 7: "#168c82"}
BACKGROUND = "#fcfcfa"


def position(phase, radius=1):
    return (radius * sin(2 * pi * float(phase)), radius * cos(2 * pi * float(phase)))


def draw_common_circle(ax, atoms, occupancy):
    ax.add_patch(patches.Circle((0, 0), 1, fill=False, color="#b7c0c8", lw=1))
    for atom in sorted(atoms, key=lambda atom: atom[0]):
        points = [position(phase) for phase in core.sites(atom)]
        # Polygon edges identify each point set; they are not additional bonds.
        ax.plot(
            [point[0] for point in (*points, points[0])],
            [point[1] for point in (*points, points[0])],
            color=COLORS[atom[0]],
            lw=0.7 if atom[0] == 2 else 1.0,
            alpha=0.30 if atom[0] == 2 else 0.50,
        )
    for phase, owners in occupancy.items():
        for half, owner in enumerate(owners):
            ax.add_patch(
                patches.Wedge(
                    position(phase),
                    0.012,
                    90 + 180 * half,
                    270 + 180 * half,
                    facecolor=COLORS[atoms[owner][0]],
                    edgecolor=BACKGROUND,
                    linewidth=0.3,
                    zorder=5,
                )
            )
    ax.text(0, 1.12, "0 turns", ha="center", fontsize=10, color="#526270")
    ax.set_title("All 33 atoms on their common circle", fontsize=17, pad=20)
    ax.text(
        0.5,
        -0.045,
        "Each coloured polygon is an atom.\n"
        "Each two-colour dot is one point shared by two atoms.",
        transform=ax.transAxes,
        ha="center",
        va="top",
        fontsize=11,
        color="#526270",
        linespacing=1.6,
    )


def draw_separated_rings(ax, atoms, occupancy, graph):
    radii = [0.30 + 0.022 * i for i in range(len(atoms))]
    cycle_pairs = {frozenset((i, (i + 1) % 7)) for i in range(7)}
    for phase, owners in occupancy.items():
        points = [position(phase, radii[i]) for i in owners]
        cycle_bond = frozenset(owners) in cycle_pairs
        ax.plot(
            [point[0] for point in points],
            [point[1] for point in points],
            color="#c73043" if cycle_bond else "#a2aeb7",
            lw=2 if cycle_bond else 0.65,
            alpha=1 if cycle_bond else 0.65,
            zorder=2 if cycle_bond else 1,
        )
    for i, atom in enumerate(atoms):
        ax.add_patch(
            patches.Circle(
                (0, 0),
                radii[i],
                fill=False,
                lw=0.55,
                color=COLORS[atom[0]],
                alpha=0.65,
            )
        )
        points = [position(phase, radii[i]) for phase in core.sites(atom)]
        ax.scatter(
            [point[0] for point in points],
            [point[1] for point in points],
            s=13,
            c=COLORS[atom[0]],
            edgecolors=BACKGROUND,
            linewidths=0.3,
            zorder=4,
        )
    assert all(graph.has_edge(i, (i + 1) % 7) for i in range(7))
    ax.set_title("The same points, with rings separated", fontsize=17, pad=20)
    ax.text(
        0.5,
        -0.045,
        "One ring per atom; angles are unchanged.\n"
        "Spokes join paired sites. Red spokes trace the seven-cycle.",
        transform=ax.transAxes,
        ha="center",
        va="top",
        fontsize=11,
        color="#526270",
        linespacing=1.6,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--outdir", type=Path, default=Path(__file__).parent / "output")
    args = parser.parse_args()
    atoms = counterexample.construct()
    occupancy, graph = core.analyze(atoms)
    assert len(atoms) == 33 and len(occupancy) == 52
    assert all(len(owners) == 2 for owners in occupancy.values())
    assert not nx.is_bipartite(graph)

    fig, axes = plt.subplots(1, 2, figsize=(16, 9), facecolor=BACKGROUND)
    draw_common_circle(axes[0], atoms, occupancy)
    draw_separated_rings(axes[1], atoms, occupancy, graph)
    for ax in axes:
        ax.set_aspect("equal")
        ax.set_xlim(-1.14, 1.14)
        ax.set_ylim(-1.14, 1.14)
        ax.axis("off")
    fig.suptitle(
        "The actual cyclic-atom molecule",
        fontsize=23,
        color="#263e4e",
        y=0.97,
    )
    fig.text(
        0.5,
        0.915,
        "19 × 2-atoms   +   6 × 3-atoms   +   4 × 5-atoms   +   4 × 7-atoms",
        ha="center",
        fontsize=12,
        color="#526270",
    )
    fig.legend(
        handles=[
            Line2D(
                [], [], color=color, lw=2, marker="o", markersize=5, label=f"{p}-atom"
            )
            for p, color in COLORS.items()
        ],
        loc="lower center",
        bbox_to_anchor=(0.5, 0.025),
        ncol=4,
        frameon=False,
        fontsize=11,
    )
    fig.text(
        0.5,
        0.012,
        "All 52 occupied circle positions are paired exactly. "
        "Interior crossings of polygon edges are not sites or bonds.",
        ha="center",
        fontsize=10,
        color="#526270",
    )
    fig.subplots_adjust(left=0.025, right=0.975, top=0.83, bottom=0.18, wspace=0.08)
    args.outdir.mkdir(parents=True, exist_ok=True)
    for extension in ("png", "svg"):
        output = args.outdir / f"nonbipartite_molecule_circle.{extension}"
        fig.savefig(output, dpi=200, facecolor=BACKGROUND)
        print(output)
    plt.close(fig)


if __name__ == "__main__":
    main()
