"""Draw the exact 33-atom counterexample as two rings joined by 2-atoms.

Run from the repository root: python -m visualization.plot_nonbipartite
"""

from math import cos, pi, sin
from pathlib import Path

import matplotlib

matplotlib.use("Agg")

import matplotlib.pyplot as plt
import networkx as nx
from matplotlib.lines import Line2D

import verification.check_bipartiteness_counterexample as counterexample
import visualization.core as core


def main():
    atoms = counterexample.construct()
    _, graph = core.analyze(atoms)
    assert not nx.is_bipartite(graph)
    colors = {2: "#dce3e8", 3: "#d8c8ec", 5: "#f5d59d", 7: "#a6dbd2"}
    angles = [pi / 2 - 2 * pi * i / 7 for i in range(7)]
    positions = {
        layer * 7 + i: (radius * cos(angle), radius * sin(angle))
        for layer, radius in enumerate((1.65, 4.0))
        for i, angle in enumerate(angles)
    }
    for i, angle in enumerate(angles):
        bridges = sorted(node for node in graph.neighbors(i) if node >= 14)
        for j, node in enumerate(bridges):
            assert set(graph.neighbors(node)) == {i, i + 7}
            bridge_angle = angle + (j - (len(bridges) - 1) / 2) * 0.13
            positions[node] = (2.80 * cos(bridge_angle), 2.80 * sin(bridge_angle))

    fig, ax = plt.subplots(figsize=(11, 11), facecolor="#fbfcfd")
    ax.set_facecolor("#fbfcfd")
    nx.draw_networkx_edges(
        graph,
        positions,
        edgelist=[(u, v) for u, v in graph.edges() if u >= 14 or v >= 14],
        ax=ax,
        edge_color="#9baab6",
        width=1.5,
    )
    nx.draw_networkx_edges(
        graph,
        positions,
        edgelist=[(7 + i, 7 + (i + 1) % 7) for i in range(7)],
        ax=ax,
        edge_color="#667b89",
        width=2.3,
    )
    nx.draw_networkx_edges(
        graph,
        positions,
        edgelist=[(i, (i + 1) % 7) for i in range(7)],
        ax=ax,
        edge_color="#ce3d49",
        width=4.2,
    )
    nx.draw_networkx_nodes(
        graph,
        positions,
        nodelist=list(range(14, 33)),
        node_color=colors[2],
        edgecolors="#748693",
        linewidths=1.1,
        node_size=200,
        ax=ax,
    )
    nx.draw_networkx_nodes(
        graph,
        positions,
        nodelist=list(range(14)),
        node_color=[colors[atom[0]] for atom in atoms[:14]],
        edgecolors="#334b5b",
        linewidths=1.5,
        node_size=1000,
        ax=ax,
    )
    nx.draw_networkx_labels(
        graph,
        positions,
        labels={
            layer * 7 + i: f"{letter}{'₀' if layer == 0 else '₁'}"
            for layer in range(2)
            for i, letter in enumerate("ABCDEFH")
        },
        font_size=13,
        font_color="#203849",
        font_weight="medium",
        ax=ax,
    )
    ax.text(
        0,
        0.12,
        "7-cycle",
        ha="center",
        va="center",
        fontsize=19,
        fontweight="bold",
        color="#bd303d",
    )
    ax.text(
        0,
        -0.25,
        "cannot be two-coloured",
        ha="center",
        va="center",
        fontsize=11,
        color="#536b7b",
    )
    ax.set_title(
        "A non-bipartite molecule",
        fontsize=23,
        fontweight="medium",
        color="#203849",
        pad=31,
    )
    ax.text(
        0.5,
        1.014,
        "33 atoms · 52 bonds · every occupied site is paired",
        transform=ax.transAxes,
        ha="center",
        color="#536b7b",
        fontsize=12,
    )
    ax.legend(
        handles=[
            Line2D(
                [],
                [],
                linestyle="none",
                marker="o",
                markerfacecolor=colors[p],
                markeredgecolor="#526b7b",
                markersize=9,
                label=f"{p}-atom",
            )
            for p in (2, 3, 5, 7)
        ],
        loc="lower center",
        bbox_to_anchor=(0.5, -0.048),
        ncol=4,
        frameon=False,
        fontsize=11,
    )
    ax.set_xlim(-4.65, 4.65)
    ax.set_ylim(-4.4, 4.5)
    ax.set_aspect("equal")
    ax.axis("off")
    fig.text(
        0.5,
        0.035,
        "Each node is an atom; each line is a bond. The 19 small nodes join the two copies.",
        ha="center",
        fontsize=11,
        color="#536b7b",
    )
    fig.subplots_adjust(left=0.035, right=0.965, top=0.88, bottom=0.10)
    output = Path(
        "C:/Users/roxy/.codex/visualizations/2026/11/15/"
        "01a1e0b3-cc55-7ba2-9d74-2faad2941633/nonbipartite_molecule"
    )
    fig.savefig(output.with_suffix(".png"), dpi=180, facecolor=fig.get_facecolor())
    fig.savefig(output.with_suffix(".svg"), facecolor=fig.get_facecolor())
    plt.close(fig)
    print(output.with_suffix(".png"))


if __name__ == "__main__":
    main()
