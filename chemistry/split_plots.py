"""Graph and curved in/out drawings of the minimum-cut splitting reaction."""

import matplotlib.pyplot as plt
import networkx as nx
import numpy as np
from matplotlib.lines import Line2D
from matplotlib.patches import FancyArrowPatch

import chemistry.model as model
import chemistry.plots as plots
import visualization.core as core


def cut_graphs(reaction, outdir):
    atoms = reaction["maximum"]
    _, graph = core.analyze(atoms)
    positions = plots.maximum_positions(atoms)
    fig, axes = plt.subplots(2, 2, figsize=(13, 15))
    for row, element, count, title in (
        (0, 7, 35, "A and B: remove the five 7-atoms (two copies)"),
        (1, 5, 70, "C: remove the fourteen 5-atoms (one copy)"),
    ):
        cuts = [
            (i, j) for i, j in graph.edges() if element in (atoms[i][0], atoms[j][0])
        ]
        kept = graph.copy()
        kept.remove_edges_from(cuts)
        for ax, shown in zip(axes[row], (graph, kept)):
            plots.draw_graph(
                ax, atoms, positions, graph=shown, size=100, alpha=0.38, curved=True
            )
            ax.set_xlim(-2, 6)
            ax.set_ylim(-6.7, 2)
        for i, j in cuts:
            axes[row, 0].add_patch(
                FancyArrowPatch(
                    positions[i],
                    positions[j],
                    connectionstyle="arc3,rad=0.12",
                    arrowstyle="-",
                    color=plots.CUT,
                    linewidth=1,
                    alpha=0.8,
                    linestyle="dashed",
                    shrinkA=3,
                    shrinkB=3,
                )
            )
        axes[row, 0].set_title(title, fontsize=13, pad=20)
        axes[row, 1].set_title(
            "7 × F35 + 5 free 7-atoms" if element == 7 else "5 × F37 + 14 free 5-atoms",
            fontsize=14,
            pad=20,
        )
        axes[row, 0].text(
            0.5,
            -0.025,
            f"{count} bonds cut per copy",
            transform=axes[row, 0].transAxes,
            ha="center",
            fontsize=12,
            color=plots.CUT,
        )
        axes[row, 1].text(
            0.5,
            -0.025,
            (
                "Each row remains a bonded 7-atom fragment."
                if element == 7
                else "Each column remains a bonded 8-atom fragment."
            ),
            transform=axes[row, 1].transAxes,
            ha="center",
            fontsize=12,
        )
    fig.suptitle(
        "Break 2 × 35 + 70 = 140 bonds; keep the fragments", fontsize=20, y=0.98
    )
    plots.legend(fig)
    fig.subplots_adjust(top=0.91, bottom=0.08, hspace=0.25, wspace=0.2)
    plots.save(fig, outdir, "minimum_split_cuts")


def bipartite_positions(atoms):
    threes = [i for i, atom in enumerate(atoms) if atom[0] == 3]
    partners = [i for i, atom in enumerate(atoms) if atom[0] != 3]
    return {
        **{node: (x, 0) for node, x in zip(threes, np.linspace(-2, 2, len(threes)))},
        **{
            node: (x, 1.8)
            for node, x in zip(partners, np.linspace(-1.5, 1.5, len(partners)))
        },
    }


def completion_graphs(reaction, outdir):
    fig, axes = plt.subplots(2, 3, figsize=(16, 9))
    for row, group, product, extra, copies in (
        (0, reaction["row_fragments"][0], reaction["product_groups"][0], 5, 14),
        (1, reaction["column_fragments"][0], reaction["product_groups"][14], 7, 5),
    ):
        final = reaction["stages"][-1]["atoms"]
        atoms = tuple(final[i] for i in product)
        positions = bipartite_positions(atoms)
        _, full = core.analyze(atoms)
        old = full.subgraph(range(len(group))).copy()
        before = full.copy()
        new_edges = [
            (i, j) for i, j in full.edges() if i >= len(group) or j >= len(group)
        ]
        before.remove_edges_from(new_edges)
        for ax, shown in zip(axes[row], (old, before, full)):
            visible = tuple(atoms[i] for i in shown)
            # draw_graph uses list indices, so retain the original contiguous IDs.
            plots.draw_graph(
                ax, visible, positions, graph=shown, labels=True, size=330, alpha=0.45
            )
            ax.set_xlim(-2.6, 2.6)
            ax.set_ylim(-0.8, 2.8)
        nx.draw_networkx_edges(
            full,
            positions,
            edgelist=new_edges,
            ax=axes[row, 2],
            edge_color=plots.NEW,
            width=2,
        )
        for i in range(len(group)):
            if atoms[i][0] == 3:
                for d in range(3 - old.degree(i)):
                    axes[row, 0].plot(
                        (positions[i][0] + (d - 0.5) * 0.12,) * 2,
                        (-0.12, -0.32),
                        color=plots.CUT,
                        linewidth=1.8,
                    )
        axes[row, 0].set_title(
            f"F3{extra}: {len(group)} atoms kept together", fontsize=14
        )
        axes[row, 1].set_title(
            f"Add {'one 5-atom' if extra == 5 else 'two 7-atoms'} "
            "from the other source",
            fontsize=13,
        )
        axes[row, 2].set_title(f"{copies} copies of M3{extra}", fontsize=15)
        axes[row, 0].text(
            0.5,
            -0.02,
            f"{old.number_of_edges()} original bonds retained per fragment",
            transform=axes[row, 0].transAxes,
            ha="center",
            fontsize=11,
        )
        axes[row, 2].text(
            0.5,
            -0.02,
            f"{len(new_edges)} new bonds per product",
            transform=axes[row, 2].transAxes,
            ha="center",
            fontsize=11,
            color=plots.NEW,
        )
    fig.suptitle("Complete the retained fragments", fontsize=21, y=0.98)
    plots.legend(fig, (Line2D([], [], color=plots.NEW, label="new bond"),))
    fig.subplots_adjust(top=0.88, bottom=0.1, wspace=0.2, hspace=0.32)
    plots.save(fig, outdir, "minimum_split_completion")


def all_stages(reaction, outdir):
    fig, axes = plt.subplots(1, 5, figsize=(25, 11))
    for ax, stage in zip(axes, reaction["stages"]):
        atoms = stage["atoms"]
        occupancy, graph = model.inspect_open(atoms)
        components = sorted(
            nx.connected_components(graph), key=lambda c: (-len(c), min(c))
        )
        positions = {}
        large = [component for component in components if len(component) > 10]
        small = [component for component in components if 1 < len(component) <= 10]
        free = [
            next(iter(component)) for component in components if len(component) == 1
        ]
        for row, component in enumerate(large):
            for node, point in plots.maximum_positions(reaction["maximum"]).items():
                positions[node + min(component)] = (
                    point[0] * 0.55,
                    point[1] * 0.55 - row * 5,
                )
        for k, component in enumerate(small):
            nodes = sorted(component)
            local = tuple(atoms[i] for i in nodes)
            for i, (x, y) in bipartite_positions(local).items():
                positions[nodes[i]] = (
                    x * 0.36 + (k % 2) * 2.6,
                    y * 0.36 - (k // 2) * 1.6 - len(large) * 5,
                )
        bottom = -max(1, len(large) * 5 + ((len(small) + 1) // 2) * 1.6) - 0.5
        for k, node in enumerate(free):
            positions[node] = (k % 10 * 0.42 - 0.4, bottom - (k // 10) * 0.6)
        plots.draw_graph(
            ax, atoms, positions, graph=graph, size=20, alpha=0.3, curved=bool(large)
        )
        sockets = sum(len(owners) == 1 for owners in occupancy.values())
        ax.set_title(
            stage["name"] + f"\n{graph.number_of_edges()} bonds · {sockets} open sites",
            fontsize=12,
            pad=18,
        )
        ax.text(
            0.5,
            -0.025,
            f"{len(components)} components",
            transform=ax.transAxes,
            ha="center",
            fontsize=12,
        )
    fig.suptitle(
        "All 162 atoms at five stages of the 140-cut reaction", fontsize=22, y=0.97
    )
    fig.text(
        0.5,
        0.07,
        "Layouts regroup connected components at each stage. "
        "Every dot is an actual atom; colours identify elements.",
        ha="center",
        fontsize=12,
    )
    plots.legend(fig)
    fig.subplots_adjust(top=0.88, bottom=0.13, left=0.02, right=0.98, wspace=0.3)
    plots.save(fig, outdir, "minimum_split_stages")


def human_curves(ax, atoms):
    """The curved in/out style of humanity/visualiser.py, with exact contact angles.

    Radii separate the curves for readability. Only the marked sites are atom
    points; incidental crossings of the interpolating curves are not bonds.
    """
    occupancy, graph = model.inspect_open(atoms)
    colors = nx.bipartite.color(graph)
    # Prefer all 3-atoms inside for the molecules and fragments used here.
    for component in nx.connected_components(graph):
        first = next((i for i in component if atoms[i][0] == 3), min(component))
        if colors[first] != 0:
            for i in component:
                colors[i] = 1 - colors[i]
    angles = np.unique(
        np.r_[
            np.linspace(0, 2 * np.pi, 30001), [2 * np.pi * float(x) for x in occupancy]
        ]
    )
    for side in (0, 1):
        nodes = [i for i in graph if colors[i] == side]
        for k, node in enumerate(nodes):
            p, phase, _ = atoms[node]
            base = (
                (0.22 + 0.58 * k / max(1, len(nodes) - 1))
                if side == 0
                else (1.2 + 0.58 * k / max(1, len(nodes) - 1))
            )
            radius = base + (1 - base) * np.exp(
                -60 / p * np.abs(np.sin(p * (angles / 2 - float(phase) * np.pi)))
            )
            ax.plot(
                -radius * np.sin(angles),
                radius * np.cos(angles),
                color=core.COLORS[p],
                lw=0.9,
                alpha=0.86,
            )
    circle = np.linspace(0, 2 * np.pi, 1000)
    ax.plot(
        -np.sin(circle),
        np.cos(circle),
        color="#bcc5d1",
        lw=0.4,
        alpha=0.45,
        linestyle=":",
    )
    for paired in (True, False):
        sites = [
            2 * np.pi * float(x)
            for x, owners in occupancy.items()
            if (len(owners) == 2) == paired
        ]
        ax.scatter(
            -np.sin(sites),
            np.cos(sites),
            s=8 if paired else 25,
            facecolor="#e1e8ef" if paired else "#111825",
            edgecolor="#e1e8ef" if paired else "#ef737b",
            linewidth=0.7,
            zorder=5,
        )
    ax.set_xlim(-1.9, 1.9)
    ax.set_ylim(-1.9, 1.9)
    ax.set_aspect("equal")
    ax.axis("off")


def human_reaction(reaction, outdir):
    fig, axes = plt.subplots(1, 3, figsize=(17, 7), facecolor="#111825")
    for ax, atoms, title, formula in (
        (axes[0], reaction["maximum"], "3 × maximum molecule", "3₃₅ 5₁₄ 7₅"),
        (axes[1], model.binary_molecule(3, 5), "14 × M35", "3₅ 5₃"),
        (axes[2], model.binary_molecule(3, 7), "5 × M37", "3₇ 7₃"),
    ):
        human_curves(ax, atoms)
        ax.set_title(title, color="white", fontsize=17, pad=18)
        ax.text(
            0.5,
            -0.04,
            formula,
            transform=ax.transAxes,
            ha="center",
            color="white",
            fontsize=16,
        )
    fig.text(0.355, 0.51, "→", color="white", fontsize=35, ha="center")
    fig.text(0.675, 0.51, "+", color="white", fontsize=30, ha="center")
    fig.text(
        0.5,
        0.09,
        "One curve per atom. Marked contacts on the dotted circle are bonds; "
        "other curve crossings are not bonds.",
        color="#c4ceda",
        fontsize=12,
        ha="center",
    )
    fig.legend(
        handles=[
            Line2D([], [], color=core.COLORS[p], label=f"{p}-atom") for p in (3, 5, 7)
        ],
        loc="lower center",
        ncol=3,
        frameon=False,
        labelcolor="white",
        fontsize=12,
    )
    fig.subplots_adjust(top=0.88, bottom=0.2, wspace=0.18, left=0.02, right=0.98)
    for suffix in ("png", "svg"):
        fig.savefig(
            outdir / f"minimum_split_human.{suffix}",
            dpi=200,
            facecolor=fig.get_facecolor(),
        )
    plt.close(fig)


def human_fragments(reaction, outdir):
    fig, axes = plt.subplots(1, 2, figsize=(12, 7), facecolor="#111825")
    for ax, group, title in (
        (axes[0], reaction["row_fragments"][0], "14 × F35: five open sites each"),
        (axes[1], reaction["column_fragments"][0], "5 × F37: fourteen open sites each"),
    ):
        human_curves(ax, tuple(reaction["maximum"][i % 54] for i in group))
        ax.set_title(title, color="white", fontsize=16, pad=18)
    fig.text(
        0.5,
        0.1,
        "Hollow red circles are open sites. Complete F35 with one free 5-atom, "
        "and F37 with two free 7-atoms.",
        color="#c4ceda",
        fontsize=12,
        ha="center",
    )
    fig.subplots_adjust(top=0.88, bottom=0.2, left=0.02, right=0.98, wspace=0.1)
    for suffix in ("png", "svg"):
        fig.savefig(
            outdir / f"minimum_split_fragments_human.{suffix}",
            dpi=200,
            facecolor=fig.get_facecolor(),
        )
    plt.close(fig)
