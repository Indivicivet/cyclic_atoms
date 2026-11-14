"""Enumerate balanced closed reactions with at most two molecules per side.

Species are formulas, not geometric isomers. Every formula has an exact witness
from the complete three-prime parity classification, binary molecules or dimers.
An instantaneous reaction is defined here by its closed endpoints; this does
not assert a continuous motion or an underlying path without free atoms.
"""

import json
from collections import defaultdict
from fractions import Fraction
from itertools import combinations_with_replacement
from pathlib import Path

import chemistry.examples as examples
import chemistry.model as model
import visualization.core as core


def catalog():
    witnesses = {}
    for row in examples.weight_table():
        if row["connected_three_element"]:
            formula = (row["n3"], row["n5"], row["n7"])
            witnesses[formula] = model.weight_configuration(
                (3, 5, 7), (row["a"], row["b"], row["c"])
            )
    for p, q in ((3, 5), (3, 7), (5, 7)):
        atoms = model.binary_molecule(p, q)
        witnesses[tuple(model.formula(atoms).get(p, 0) for p in (3, 5, 7))] = atoms
    for p in (3, 5, 7):
        witnesses[tuple(2 if q == p else 0 for q in (3, 5, 7))] = (
            (p, Fraction(0), None),
        ) * 2
    return dict(sorted(witnesses.items()))


def inventory(side):
    return tuple(sum(molecule[i] for molecule in side) for i in range(3))


def reactions(witnesses):
    by_inventory = defaultdict(list)
    for molecule in witnesses:
        by_inventory[molecule].append((molecule,))
    for pair in combinations_with_replacement(witnesses, 2):
        by_inventory[inventory(pair)].append(pair)
    return tuple(
        (left, right)
        for sides in by_inventory.values()
        for left, right in combinations_with_replacement(sides, 2)
        if left != right
    )


def maximum_products(witnesses):
    """Orient nontrivial 2->2 channels to put Tmax on the product side."""
    maximum = (35, 14, 5)
    return tuple(
        sorted(
            (
                (left, right) if maximum in right else (right, left)
                for left, right in reactions(witnesses)
                if len(left) == len(right) == 2 and maximum in left + right
            ),
            key=lambda channel: (
                sum(inventory(channel[0])),
                max(map(sum, channel[0])),
                channel,
            ),
        )
    )


def maximum_exchange():
    """Closed endpoints of M35 + T(30,13,5) -> Tmax + D5.

    The reactant supports intersect in one 5-atom's point set. Splicing out
    those two 5-atoms creates five cross-bonds and a five-bond dimer. The
    returned fragments describe the geometry, not a required open intermediate.
    """
    small = model.rotate(model.binary_molecule(3, 5), Fraction(6, 105))
    large = model.weight_configuration((3, 5, 7), (1, 0, 6))
    roots = next(
        (i, j)
        for i, atom in enumerate(small)
        for j, other in enumerate(large)
        if atom[0] == other[0] == 5 and set(core.sites(atom)) == set(core.sites(other))
    )
    fragments = (
        tuple(atom for i, atom in enumerate(small) if i != roots[0]),
        tuple(atom for i, atom in enumerate(large) if i != roots[1]),
    )
    return {
        "reactants": (small, large),
        "roots": roots,
        "fragments": fragments,
        "products": (
            model.join(fragments, (Fraction(0), Fraction(0))),
            model.join(
                ((small[roots[0]],), (large[roots[1]],)), (Fraction(0), Fraction(0))
            ),
        ),
    }


def main():
    witnesses = catalog()
    for atoms in witnesses.values():
        core.analyze(atoms)
    channels = reactions(witnesses)
    maximum = (35, 14, 5)
    outgoing = [
        (left, right)
        for left, right in channels
        if all(molecule == maximum for molecule in left)
        or all(molecule == maximum for molecule in right)
    ]
    summary = {
        "formula_count": len(witnesses),
        "channel_counts": {
            f"{a}_to_{b}": sum(
                sorted((len(left), len(right))) == [a, b] for left, right in channels
            )
            for a, b in ((1, 1), (1, 2), (2, 2))
        },
        "maximum_outgoing": outgoing,
        "maximum_as_product": maximum_products(witnesses),
        "maximum_exchange": maximum_exchange(),
        "species": [
            {"formula": formula, "atoms": atoms} for formula, atoms in witnesses.items()
        ],
        "reactions": channels,
    }
    output = Path(__file__).parent / "output" / "closed_reactions.json"
    output.parent.mkdir(exist_ok=True)
    output.write_text(
        json.dumps(summary, default=str, indent=2) + "\n", encoding="utf-8"
    )
    print("Species formulas:", len(witnesses))
    print("Channels:", summary["channel_counts"])
    print("Outgoing channels from one or two maxima:", outgoing)
    print("Channels producing Tmax:", len(summary["maximum_as_product"]))
    for left, right in summary["maximum_as_product"]:
        print(
            left,
            "->",
            right,
            "sizes",
            tuple(map(sum, left)),
            "->",
            tuple(map(sum, right)),
        )
    print(
        "Example 1->2:", next(((l, r) for l, r in channels if len(l) != len(r)), None)
    )
    print(
        "Example 2->2:",
        next(((l, r) for l, r in channels if len(l) == len(r) == 2), None),
    )


if __name__ == "__main__":
    main()
