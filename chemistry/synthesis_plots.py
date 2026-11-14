"""Draw the seven-event and four-type syntheses from M35 and M57.

Run from the repository root: python -m chemistry.synthesis_plots
"""

import argparse
import json
from fractions import Fraction
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.lines import Line2D
from matplotlib.patches import FancyArrowPatch

import chemistry.closed_reactions as closed
import chemistry.model as model
import chemistry.plots as plots
import chemistry.split_plots as split_plots
import chemistry.synthesis as synthesis
import visualization.core as core

BACKGROUND = "#111825"


def molecules():
    return {
        "A": model.binary_molecule(3, 5),
        "D5": ((5, Fraction(0), None),) * 2,
        **{f"X{k}": model.weight_configuration((3, 5, 7), (1, 0, k)) for k in range(8)},
    }


def growth_positions(atoms):
    """Keep each CRT slice in the same row throughout X0,...,X7."""
    positions = {}
    caps = [
        i
        for i, (p, phase, _) in enumerate(atoms)
        if p == 5 and int(phase * 105) % 3 == 0
    ]
    cap_x = dict(zip(caps, np.linspace(-0.6, 4.6, len(caps))))
    for i, (p, phase, _) in enumerate(atoms):
        x, y, z = (int(phase * 105) % n for n in (3, 5, 7))
        if p == 3:
            positions[i] = (y, -z - 1)
        elif p == 7:
            positions[i] = (y, 0)
        elif i in cap_x:
            positions[i] = (cap_x[i], 1.3)
        else:
            positions[i] = (-1.2 if x == 1 else 5.2, -z - 1)
    return positions


def draw_molecule(ax, name, atoms, human=False, fixed_grid=False):
    if human:
        split_plots.human_curves(ax, atoms)
    elif name == "D5":
        for bend in (-0.75, -0.35, 0, 0.35, 0.75):
            ax.add_patch(
                FancyArrowPatch(
                    (-0.6, 0),
                    (0.6, 0),
                    connectionstyle=f"arc3,rad={bend}",
                    arrowstyle="-",
                    linewidth=1.4,
                    color=plots.INK,
                    shrinkA=8,
                    shrinkB=8,
                )
            )
        ax.scatter((-0.6, 0.6), (0, 0), marker="s", color=core.COLORS[5], s=130)
        ax.set_xlim(-1.3, 1.3)
        ax.set_ylim(-1, 1)
        ax.set_aspect("equal")
        ax.axis("off")
    else:
        positions = (
            split_plots.bipartite_positions(atoms)
            if name == "A"
            else growth_positions(atoms)
        )
        plots.draw_graph(ax, atoms, positions, size=40, alpha=0.5, curved=True)
        if fixed_grid:
            ax.set_xlim(-1.8, 5.8)
            ax.set_ylim(-7.6, 2)


def formula_label(atoms):
    subscript = str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")
    return " ".join(
        f"{p}{str(n).translate(subscript)}" for p, n in model.formula(atoms).items()
    )


def name_label(name):
    if name == "X0":
        return "X₀ = M57"
    if name == "X7":
        return "X₇ = MAX"
    if name == "A":
        return "A = M35"
    return name.translate(str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉"))


def finish(fig, outdir, name, human):
    color = "white" if human else plots.INK
    fig.legend(
        handles=[
            Line2D(
                [],
                [],
                color=core.COLORS[p],
                marker=core.SHAPES[p],
                linestyle="-" if human else "none",
                label=f"{p}-atom",
            )
            for p in (3, 5, 7)
        ],
        loc="lower center",
        ncol=3,
        frameon=False,
        labelcolor=color,
        fontsize=11,
    )
    for suffix in ("png", "svg"):
        fig.savefig(outdir / f"{name}.{suffix}", dpi=190, facecolor=fig.get_facecolor())
    plt.close(fig)


def ladder(data, outdir, human=False):
    fig = plt.figure(figsize=(18, 12), facecolor=BACKGROUND if human else "white")
    color = "white" if human else plots.INK
    order = ((0, 1, 2, 3), (7, 6, 5, 4))
    for row, values in enumerate(order):
        for col, k in enumerate(values):
            ax = fig.add_axes((0.025 + col * 0.245, 0.51 - row * 0.39, 0.22, 0.33))
            name = f"X{k}"
            draw_molecule(ax, name, data[name], human, fixed_grid=True)
            ax.set_title(name_label(name), color=color, fontsize=16, pad=8)
            ax.text(
                0.5,
                -0.06,
                formula_label(data[name]),
                transform=ax.transAxes,
                ha="center",
                color=color,
                fontsize=12,
            )
    for row in range(2):
        for col in range(3):
            x = 0.255 + col * 0.245
            start, end = (x - 0.012, x + 0.025) if row == 0 else (x + 0.025, x - 0.012)
            y = 0.675 - row * 0.39
            fig.add_artist(
                FancyArrowPatch(
                    (start, y),
                    (end, y),
                    transform=fig.transFigure,
                    arrowstyle="->",
                    mutation_scale=20,
                    color=color,
                    lw=1.6,
                )
            )
            step = col + 1 if row == 0 else 7 - col
            fig.text(
                x + 0.005, y + 0.035, f"R{step}", color=color, ha="center", fontsize=12
            )
    fig.add_artist(
        FancyArrowPatch(
            (0.987, 0.66),
            (0.987, 0.3),
            transform=fig.transFigure,
            arrowstyle="->",
            mutation_scale=20,
            color=color,
            lw=1.6,
        )
    )
    fig.text(0.982, 0.475, "R4", color=color, fontsize=12, ha="right")
    fig.suptitle(
        "Seven events: add one M35 and release one D5 at every arrow",
        color=color,
        fontsize=20,
        y=0.97,
    )
    fig.text(
        0.5,
        0.915,
        "7 M35 + M57 → MAX + 7 D5     ·     each of R1–R7 fires once",
        color=color,
        ha="center",
        fontsize=14,
    )
    fig.text(
        0.5,
        0.07,
        "Read the top row left to right, then the bottom row right to left. "
        + (
            "Each curve is an atom; marked circle contacts are bonds."
            if human
            else "Each vertex is an atom; curve crossings are not vertices."
        ),
        color=color,
        ha="center",
        fontsize=11,
    )
    finish(
        fig,
        outdir,
        "synthesis_seven_human" if human else "synthesis_seven_graphs",
        human,
    )


def four_types(data, outdir, human=False):
    fig = plt.figure(figsize=(18, 17), facecolor=BACKGROUND if human else "white")
    color = "white" if human else plots.INK
    reactions = (
        (("A", "X0"), ("X1", "D5"), 4),
        (("A", "X1"), ("X2", "D5"), 4),
        (("X2", "X2"), ("X4", "X0"), 2),
        (("X4", "X4"), ("X7", "X1"), 1),
    )
    for row, (left, right, count) in enumerate(reactions):
        bottom = 0.715 - row * 0.215
        for col, name in enumerate(left + right):
            x = (0.025, 0.245, 0.57, 0.79)[col]
            ax = fig.add_axes((x, bottom, 0.185, 0.17))
            draw_molecule(ax, name, data[name], human)
            fig.text(
                x + 0.0925,
                bottom + 0.187,
                name_label(name),
                color=color,
                fontsize=14,
                ha="center",
            )
            fig.text(
                x + 0.0925,
                bottom - 0.014,
                formula_label(data[name]),
                ha="center",
                color=color,
                fontsize=11,
            )
        for x in (0.225, 0.77):
            fig.text(
                x,
                bottom + 0.08,
                "+",
                ha="center",
                va="center",
                color=color,
                fontsize=22,
            )
        fig.add_artist(
            FancyArrowPatch(
                (0.455, bottom + 0.08),
                (0.555, bottom + 0.08),
                transform=fig.transFigure,
                arrowstyle="->",
                mutation_scale=22,
                color=color,
                lw=1.5,
            )
        )
        fig.text(
            0.505, bottom + 0.115, f"R{row + 1}", color=color, ha="center", fontsize=15
        )
        fig.text(
            0.505,
            bottom + 0.045,
            f"fire ×{count}",
            color=color,
            ha="center",
            fontsize=12,
        )
    fig.suptitle(
        "Four reaction types, eleven individual events",
        color=color,
        fontsize=21,
        y=0.975,
    )
    fig.text(
        0.5,
        0.935,
        "Each row is one 2→2 type. Run R1 four times, R2 four times, "
        "R3 twice, then R4 once.",
        color=color,
        ha="center",
        fontsize=13,
    )
    fig.text(
        0.5,
        0.045,
        "Batch: 8 M35 + 4 M57 → MAX + X₁ + 8 D5 + 2 M57",
        color=color,
        ha="center",
        fontsize=12,
    )
    finish(
        fig, outdir, "synthesis_four_human" if human else "synthesis_four_graphs", human
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--outdir", type=Path, default=Path(__file__).parent / "output")
    args = parser.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    data = molecules()
    for atoms in data.values():
        core.analyze(atoms)
    ladder_steps = tuple(
        (
            (model.formula(data["A"]), model.formula(data[f"X{k}"])),
            (model.formula(data[f"X{k + 1}"]), model.formula(data["D5"])),
        )
        for k in range(7)
    )
    for left, right in ladder_steps:
        if {p: sum(m.get(p, 0) for m in left) for p in (3, 5, 7)} != {
            p: sum(m.get(p, 0) for m in right) for p in (3, 5, 7)
        }:
            raise ValueError("unbalanced ladder step")
    # Verify the displayed grouped batch, rather than assuming a byproduct can
    # be borrowed from a later row.
    counts = {
        name: tuple(model.formula(atoms).get(p, 0) for p in (3, 5, 7))
        for name, atoms in data.items()
    }
    steps = (
        [((counts["A"], counts["X0"]), (counts["X1"], counts["D5"]))] * 4
        + [((counts["A"], counts["X1"]), (counts["X2"], counts["D5"]))] * 4
        + [((counts["X2"], counts["X2"]), (counts["X4"], counts["X0"]))] * 2
        + [((counts["X4"], counts["X4"]), (counts["X7"], counts["X1"]))]
    )
    batch = synthesis.audit(steps, (counts["A"], counts["X0"]))
    if any(closed.inventory(left) != closed.inventory(right) for left, right in steps):
        raise ValueError("unbalanced four-type reaction")
    (args.outdir / "synthesis_picture_data.json").write_text(
        json.dumps({"molecules": data, "four_type_batch": batch}, default=str, indent=2)
        + "\n",
        encoding="utf-8",
    )
    for human in (False, True):
        ladder(data, args.outdir, human)
        four_types(data, args.outdir, human)
    print(f"Wrote four PNG/SVG route diagrams and exact molecule data to {args.outdir}")


if __name__ == "__main__":
    main()
