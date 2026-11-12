"""Graph drawings with stable vertices, explicit cut bonds, and exact multiplicity."""

import matplotlib.pyplot as plt
import networkx as nx
import numpy as np
from matplotlib.lines import Line2D
from matplotlib.patches import FancyArrowPatch

import chemistry.model as model
import visualization.core as core

INK = "#253348"
CUT = "#c94b55"
NEW = "#238554"


def draw_graph(
    ax, atoms, positions, graph=None, labels=False, size=130, alpha=0.32, curved=False
):
    if graph is None:
        _, graph = model.inspect_open(atoms)
    if curved:
        # Straight star edges would run through intervening vertices in a grid.
        # Separate arcs keep every bond visible without introducing fake vertices.
        for i, j in graph.edges():
            ax.add_patch(
                FancyArrowPatch(
                    positions[i],
                    positions[j],
                    connectionstyle="arc3,rad=0.12",
                    arrowstyle="-",
                    color=INK,
                    alpha=alpha,
                    linewidth=0.8,
                    shrinkA=3,
                    shrinkB=3,
                )
            )
    else:
        nx.draw_networkx_edges(
            graph, positions, ax=ax, edge_color=INK, alpha=alpha, width=0.8
        )
    for p in sorted(model.formula(atoms)):
        nx.draw_networkx_nodes(
            graph,
            positions,
            nodelist=[i for i, atom in enumerate(atoms) if atom[0] == p],
            node_color=core.COLORS[p],
            node_shape=core.SHAPES[p],
            node_size=size,
            edgecolors="white",
            linewidths=0.5,
            ax=ax,
        )
    if labels:
        nx.draw_networkx_labels(
            graph,
            positions,
            labels={i: str(i) for i in graph},
            font_size=7,
            font_color="white",
            ax=ax,
        )
    ax.set_aspect("equal")
    ax.axis("off")


def legend(fig, extra=()):
    fig.legend(
        handles=[
            Line2D(
                [],
                [],
                color=core.COLORS[p],
                marker=core.SHAPES[p],
                linestyle="none",
                markersize=9,
                label=f"{p}-atom",
            )
            for p in (3, 5, 7)
        ]
        + list(extra),
        loc="lower center",
        ncol=3 + len(extra),
        frameon=False,
        fontsize=11,
    )


def save(fig, outdir, name):
    fig.savefig(outdir / f"{name}.png", dpi=180, facecolor="white")
    fig.savefig(outdir / f"{name}.svg", facecolor="white")
    plt.close(fig)


def maximum_positions(atoms):
    """Rows are z in Z7, columns are y in Z5; every dot is an actual atom."""
    positions = {}
    five_layers = sorted({int(phase * 105) % 3 for p, phase, _ in atoms if p == 5})
    for i, (p, phase, _) in enumerate(atoms):
        index = int(phase * 105)
        x, y, z = (index % n for n in (3, 5, 7))
        if p == 3:
            positions[i] = (y, -z)
        elif p == 5:
            positions[i] = (-1.2 if x == five_layers[0] else 5.2, -z)
        else:
            positions[i] = (y, 1.3)
    return positions


def maximum_graph(atoms, outdir):
    fig, ax = plt.subplots(figsize=(11, 10))
    draw_graph(ax, atoms, maximum_positions(atoms), size=185, alpha=0.42, curved=True)
    ax.set_title(
        "A maximum 3–5–7 molecule: 35 + 14 + 5 = 54 atoms", fontsize=17, pad=20
    )
    ax.text(
        0.5,
        -0.025,
        "Each row joins five 3-atoms to two 5-atoms.\n"
        "Each column joins seven 3-atoms to one 7-atom. Crossings are not vertices.",
        transform=ax.transAxes,
        ha="center",
        va="top",
        color=INK,
        fontsize=12,
    )
    legend(fig)
    fig.subplots_adjust(top=0.9, bottom=0.15, left=0.06, right=0.94)
    save(fig, outdir, "maximum_graph")


def fusion_graph(example, outdir):
    left, right = example["reactants"]
    atoms = left + right
    _, left_graph = model.inspect_open(left)
    _, right_graph = model.inspect_open(right)
    original = nx.disjoint_union(left_graph, right_graph)
    roots = (example["roots"][0], len(left) + example["roots"][1])
    positions = {}
    for offset, molecule, side, root in (
        (0, left, -1, roots[0]),
        (len(left), right, 1, roots[1]),
    ):
        remaining = [
            i + offset
            for i, atom in enumerate(molecule)
            if atom[0] == 3 and i + offset != root
        ]
        for node, y in zip(remaining, np.linspace(0.0, 3.0, len(remaining))):
            positions[node] = (side * 2.7, y)
        for node, y in zip(
            (i + offset for i, atom in enumerate(molecule) if atom[0] != 3),
            (0.4, 1.5, 2.6),
        ):
            positions[node] = (side * 1.05, y)
    positions[roots[0]] = (-1.9, 4.1)
    positions[roots[1]] = (1.9, 4.1)
    cuts = [(i, j) for i, j in original.edges() if i in roots or j in roots]
    fragments = original.copy()
    fragments.remove_edges_from(cuts)
    merged = fragments.copy()
    # Site equality determines the matching; it is not an arbitrary graph splice.
    left_sockets = {
        point: owners[0]
        for point, owners in model.inspect_open(example["fragments"][0])[0].items()
        if len(owners) == 1
    }
    right_sockets = {
        point: owners[0]
        for point, owners in model.inspect_open(example["fragments"][1])[0].items()
        if len(owners) == 1
    }
    left_ids = [i for i in range(len(left)) if i != roots[0]]
    right_ids = [i + len(left) for i in range(len(right)) if i + len(left) != roots[1]]
    bridges = [
        (left_ids[left_sockets[x]], right_ids[right_sockets[x]])
        for x in sorted(left_sockets)
    ]
    for i, j in bridges:
        positions[j] = (positions[j][0], positions[i][1])
    merged.add_edges_from(bridges)
    fig, axes = plt.subplots(1, 3, figsize=(18, 7.8))
    titles = (
        "1. Two binary molecules",
        "2. Cut six bonds",
        "3. Join the exposed sites",
    )
    for ax, graph, title in zip(axes, (original, fragments, merged), titles):
        draw_graph(ax, atoms, positions, graph=graph, labels=True, size=230, alpha=0.34)
        ax.set_title(title, fontsize=15, pad=14)
        ax.set_xlim(-3.3, 3.3)
        ax.set_ylim(-1.6, 4.6)
    for ax in axes[:2]:
        nx.draw_networkx_edges(
            original,
            positions,
            edgelist=cuts,
            ax=ax,
            edge_color=CUT,
            width=1.8,
            style="dashed",
        )
    axes[0].text(-1.85, -0.7, "M35: 3₅ 5₃", ha="center", fontsize=12)
    axes[0].text(1.85, -0.7, "M37: 3₇ 7₃", ha="center", fontsize=12)
    axes[1].text(
        0,
        -1.32,
        "6 fragment sites + 6 free-atom sites",
        ha="center",
        fontsize=11,
    )
    axes[2].text(0, 4.15, "T: 3₁₀ 5₃ 7₃", ha="center", fontsize=13, color=INK)
    nx.draw_networkx_edges(
        merged, positions, edgelist=bridges, ax=axes[2], edge_color=NEW, width=2.2
    )
    # Show the removed atoms in their product frame, with all three dimer bonds.
    for ax in axes[1:]:
        for root in roots:
            ax.scatter(
                *positions[root],
                s=310,
                facecolor="white",
                edgecolor=CUT,
                marker="^",
                zorder=5,
            )
    for ax in axes[1:]:
        for node, x in zip(roots, (-0.4, 0.4)):
            ax.scatter(x, -0.75, s=230, color=core.COLORS[3], marker="^", zorder=5)
            ax.text(
                x,
                -0.75,
                str(node),
                ha="center",
                va="center",
                color="white",
                fontsize=7,
                zorder=6,
            )
    for i, j in cuts:
        root, neighbor = (i, j) if i in roots else (j, i)
        direction = np.array(positions[root]) - positions[neighbor]
        point = np.array(positions[neighbor]) + 0.22 * direction / np.linalg.norm(
            direction
        )
        axes[1].scatter(*point, s=20, facecolor="white", edgecolor=CUT, zorder=6)
    for x in (-0.4, 0.4):
        for angle in np.deg2rad((90, 210, 330)):
            axes[1].plot(
                (x + 0.12 * np.cos(angle), x + 0.28 * np.cos(angle)),
                (-0.75 + 0.12 * np.sin(angle), -0.75 + 0.28 * np.sin(angle)),
                color=CUT,
                linewidth=1.3,
            )
    for bend in (-0.5, 0, 0.5):
        axes[2].add_patch(
            FancyArrowPatch(
                (-0.4, -0.75),
                (0.4, -0.75),
                connectionstyle=f"arc3,rad={bend}",
                arrowstyle="-",
                color=NEW,
                linewidth=1.6,
                shrinkA=8,
                shrinkB=8,
            )
        )
    axes[2].text(0, -1.32, "+ D3 (three parallel bonds)", ha="center", fontsize=11)
    fig.suptitle("M35 + M37  ⇌  T + D3", fontsize=22, y=0.97)
    legend(
        fig,
        (
            Line2D(
                [], [], color=CUT, linestyle="dashed", label="bonds to cut / cut bonds"
            ),
            Line2D([], [], color=NEW, label="new bonds"),
        ),
    )
    fig.text(
        0.5,
        0.075,
        "Vertex numbers preserve atom identity. Hollow triangles mark the extracted "
        "positions; panels use separate molecular frames.",
        ha="center",
        fontsize=10,
        color=INK,
    )
    fig.subplots_adjust(top=0.85, bottom=0.16, wspace=0.18, left=0.025, right=0.975)
    save(fig, outdir, "fusion")


def batch_split(maximum, outdir):
    fig = plt.figure(figsize=(18, 10))
    fig.suptitle("3 maximum molecules  ⇌  14 M35 + 5 M37", fontsize=22, y=0.97)
    for row in range(3):
        ax = fig.add_axes((0.03, 0.12 + 0.25 * row, 0.24, 0.22))
        draw_graph(
            ax, maximum, maximum_positions(maximum), size=16, alpha=0.32, curved=True
        )
    ax = fig.add_axes((0.34, 0.22, 0.2, 0.56))
    for p, count, top in ((3, 105, 18), (5, 42, 8), (7, 15, 2)):
        ax.scatter(
            [i % 15 for i in range(count)],
            [top - i // 15 for i in range(count)],
            c=core.COLORS[p],
            marker=core.SHAPES[p],
            s=30,
        )
        ax.text(7, top + 1.15, f"{count} × {p}-atom", ha="center", fontsize=12)
    ax.set_xlim(-1, 15)
    ax.set_ylim(-1, 21)
    ax.axis("off")
    for i in range(14):
        ax = fig.add_axes((0.625 + (i % 7) * 0.05, 0.6 - (i // 7) * 0.2, 0.045, 0.15))
        atoms = model.binary_molecule(3, 5)
        positions = {
            j: ((0 if j < 5 else 1), (j if j < 5 else j - 4) / 4) for j in range(8)
        }
        draw_graph(ax, atoms, positions, size=18, alpha=0.3)
    for i in range(5):
        ax = fig.add_axes((0.64 + i * 0.065, 0.16, 0.055, 0.16))
        atoms = model.binary_molecule(3, 7)
        positions = {
            j: ((0 if j < 7 else 1), (j if j < 7 else 2 * (j - 7) + 1) / 6)
            for j in range(10)
        }
        draw_graph(ax, atoms, positions, size=18, alpha=0.3)
    fig.text(0.15, 0.89, "3 × (3₃₅ 5₁₄ 7₅)", ha="center", fontsize=15)
    fig.text(0.44, 0.89, "One permitted intermediate", ha="center", fontsize=15)
    fig.text(0.8, 0.81, "14 × (3₅ 5₃)", ha="center", fontsize=15)
    fig.text(0.8, 0.36, "5 × (3₇ 7₃)", ha="center", fontsize=15)
    for start, end in ((0.27, 0.33), (0.55, 0.61)):
        fig.add_artist(
            FancyArrowPatch(
                (start, 0.5),
                (end, 0.5),
                transform=fig.transFigure,
                arrowstyle="<->",
                mutation_scale=20,
                color=INK,
                linewidth=1.5,
            )
        )
    fig.text(
        0.5,
        0.085,
        "Every dot is an intact atom. Full dissociation gives 630 open sites. "
        "The 162 atoms and their elements are conserved.",
        ha="center",
        fontsize=12,
    )
    legend(fig)
    fig.subplots_adjust(bottom=0.1)
    save(fig, outdir, "batch_split")


def mixed_graph(atoms, outdir):
    _, graph = core.analyze(atoms)
    bundles = ([], [], [], [], [], [])
    for i, (p, phase, _) in enumerate(atoms):
        x, y, z = (int(phase * 105) % n for n in (3, 5, 7))
        if p == 3:
            bundles[0 if y == 0 else 3].append(i)
        elif p == 5:
            bundles[1 if x == 0 else 4].append(i)
        else:
            bundles[2 if x == 0 else 5].append(i)
    positions = {}
    for bundle, angle in zip(bundles, np.deg2rad((90, 30, -30, -90, -150, 150))):
        center = 4 * np.array((np.cos(angle), np.sin(angle)))
        tangent = np.array((-np.sin(angle), np.cos(angle)))
        for node, offset in zip(bundle, np.linspace(-1.3, 1.3, len(bundle))):
            positions[node] = center + offset * tangent
    fig, ax = plt.subplots(figsize=(9, 10))
    draw_graph(ax, atoms, positions, labels=True, size=220, alpha=0.3)
    ax.set_title(
        "A 24-atom molecule using all three binary reagents", fontsize=15, pad=22
    )
    ax.text(
        0.5,
        -0.02,
        "3₁₀ 5₈ 7₆\n105 copies ⇌ 98 M35 + 80 M37 + 78 M57\n"
        "Six bundles follow the coordinate-bit classes; labels are JSON indices.",
        transform=ax.transAxes,
        ha="center",
        va="top",
        fontsize=12,
    )
    legend(fig)
    fig.subplots_adjust(top=0.9, bottom=0.2)
    save(fig, outdir, "mixed_graph")
