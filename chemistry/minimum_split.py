"""Minimum-cut reaction 3 Tmax -> 14 M35 + 5 M37.

Run from the repository root: python -m chemistry.minimum_split
"""

import argparse
import json
from fractions import Fraction
from pathlib import Path

import chemistry.model as model
import chemistry.split_plots as split_plots
import visualization.core as core


def move_atoms(atoms, indices, turns):
    """One discrete rigid rotation; atom indices and internal bonds survive."""
    return tuple(
        (
            (p, (phase + turns) % Fraction(1, p), color)
            if i in indices
            else (p, phase, color)
        )
        for i, (p, phase, color) in enumerate(atoms)
    )


def minimum_split():
    maximum = model.weight_configuration((3, 5, 7), (1, 0, 7))
    # Different cosets prevent accidental contacts between separate fragments.
    # Every unshifted site lies on the 1/105 grid; only 46 cosets are needed.
    spacing = Fraction(1, 105 * 100)
    initial = tuple(
        atom
        for copy in range(3)
        for atom in model.rotate(maximum, (copy + 1) * spacing)
    )
    row_fragments = tuple(
        tuple(
            copy * 54 + i
            for i, (p, phase, _) in enumerate(maximum)
            if p in (3, 5) and int(phase * 105) % 7 == z
        )
        for copy in range(2)
        for z in range(7)
    )
    column_fragments = tuple(
        tuple(
            108 + i
            for i, (p, phase, _) in enumerate(maximum)
            if p in (3, 7) and int(phase * 105) % 5 == y
        )
        for y in range(5)
    )
    free_fives = tuple((108 + i,) for i, atom in enumerate(maximum) if atom[0] == 5)
    free_sevens = tuple(
        (copy * 54 + i,)
        for copy in range(2)
        for i, atom in enumerate(maximum)
        if atom[0] == 7
    )
    groups = row_fragments + column_fragments + free_fives + free_sevens
    # A partition check catches omissions or duplicated atoms before any moves.
    model.fragment(initial, groups)
    extraction = tuple(
        {"indices": group, "turns": (i + 4 - (group[0] // 54 + 1)) * spacing}
        for i, group in enumerate(groups)
    )
    complete_rows = []
    for i, group in enumerate(row_fragments):
        occupancy, _ = model.inspect_open(tuple(maximum[node % 54] for node in group))
        sockets = {point for point, owners in occupancy.items() if len(owners) == 1}
        phase = min(sockets) % Fraction(1, 5)
        if set(core.sites((5, phase, None))) != sockets:
            raise ValueError("row boundary is not a single 5-atom")
        complete_rows.append(
            {
                "indices": free_fives[i],
                "turns": phase - maximum[free_fives[i][0] % 54][1] - 19 * spacing,
            }
        )
    complete_columns = []
    for i, group in enumerate(column_fragments):
        occupancy, _ = model.inspect_open(tuple(maximum[node % 54] for node in group))
        sockets = {point for point, owners in occupancy.items() if len(owners) == 1}
        phases = sorted({point % Fraction(1, 7) for point in sockets})
        if (
            len(phases) != 2
            or set().union(*(set(core.sites((7, phase, None))) for phase in phases))
            != sockets
        ):
            raise ValueError("column boundary is not two 7-atoms")
        for j, phase in enumerate(phases):
            complete_columns.append(
                {
                    "indices": free_sevens[2 * i + j],
                    "turns": phase
                    - maximum[free_sevens[2 * i + j][0] % 54][1]
                    + (14 + i - (33 + 2 * i + j)) * spacing,
                }
            )
    blocks = (
        ("Strip C's 14 five-atoms", extraction[14:33]),
        ("Strip A and B's seven-atoms", extraction[:14] + extraction[33:]),
        ("Complete fourteen M35", tuple(complete_rows)),
        ("Complete five M37", tuple(complete_columns)),
    )
    state = initial
    moves = []
    stages = [{"name": "Three maximum molecules", "after_move": 0, "atoms": initial}]
    for name, operations in blocks:
        for operation in operations:
            state = move_atoms(state, operation["indices"], operation["turns"])
            model.inspect_open(state)
            moves.append(operation)
        stages.append({"name": name, "after_move": len(moves), "atoms": state})
    return {
        "minimum_cuts": 70 * 1 + 35 * 2,
        "maximum": maximum,
        "stages": stages,
        "moves": moves,
        "row_fragments": row_fragments,
        "column_fragments": column_fragments,
        "free_fives": free_fives,
        "free_sevens": free_sevens,
        "product_groups": tuple(
            row + free_fives[i] for i, row in enumerate(row_fragments)
        )
        + tuple(
            column + free_sevens[2 * i] + free_sevens[2 * i + 1]
            for i, column in enumerate(column_fragments)
        ),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--outdir", type=Path, default=Path(__file__).parent / "output")
    args = parser.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    reaction = minimum_split()
    (args.outdir / "minimum_split_path.json").write_text(
        json.dumps(reaction, default=str, indent=2) + "\n", encoding="utf-8"
    )
    split_plots.cut_graphs(reaction, args.outdir)
    split_plots.completion_graphs(reaction, args.outdir)
    split_plots.all_stages(reaction, args.outdir)
    split_plots.human_reaction(reaction, args.outdir)
    split_plots.human_fragments(reaction, args.outdir)
    print("Minimum: 140 cuts; 175 original bonds retained; 67 rigid moves.")
    print(f"Wrote exact states and five PNG/SVG figures to {args.outdir}")


if __name__ == "__main__":
    main()
