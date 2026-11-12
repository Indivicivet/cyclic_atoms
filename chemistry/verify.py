"""Exact checks of the chemistry results. Run: python -m chemistry.verify."""

import unittest
from collections import Counter
from fractions import Fraction
from itertools import product

import networkx as nx
import numpy as np

import chemistry.closed_reactions as closed
import chemistry.examples as examples
import chemistry.minimum_split as splitting
import chemistry.model as model
import chemistry.plots as plots
import visualization.core as core


class ChemistryChecks(unittest.TestCase):
    def test_closed_reaction_catalog_and_frozen_maxima(self):
        witnesses = closed.catalog()
        self.assertEqual(len(witnesses), 86)
        self.assertEqual(max(map(sum, witnesses)), 54)
        self.assertEqual([f for f in witnesses if sum(f) == 54], [(35, 14, 5)])
        for formula, atoms in witnesses.items():
            core.analyze(atoms)
            self.assertEqual(
                tuple(model.formula(atoms).get(p, 0) for p in (3, 5, 7)), formula
            )
        channels = closed.reactions(witnesses)
        splits = [(left, right) for left, right in channels if len(left) != len(right)]
        self.assertEqual(len(splits), 2)
        self.assertEqual(
            sum(len(left) == len(right) == 2 for left, right in channels), 1657
        )
        for left, right in channels:
            self.assertEqual(closed.inventory(left), closed.inventory(right))
            self.assertFalse(all(m == (35, 14, 5) for m in left))
            self.assertFalse(all(m == (35, 14, 5) for m in right))
        self.assertEqual(
            set(splits),
            {
                (((18, 12, 6),), ((5, 3, 0), (13, 9, 6))),
                (((22, 12, 6),), ((5, 3, 0), (17, 9, 6))),
            },
        )

    def test_minimum_cut_split_every_move(self):
        reaction = splitting.minimum_split()
        state = reaction["stages"][0]["atoms"]
        original = set(model.inspect_open(state)[1].edges())
        retained = set(model.inspect_open(reaction["stages"][2]["atoms"])[1].edges())
        self.assertEqual(len(retained), 175)
        self.assertTrue(retained <= original)
        cuts = 0
        joins = 0
        for i, operation in enumerate(reaction["moves"], 1):
            before = set(model.inspect_open(state)[1].edges())
            state = splitting.move_atoms(
                state, operation["indices"], operation["turns"]
            )
            _, graph = model.inspect_open(state)
            after = set(graph.edges())
            cuts += len(before - after)
            joins += len(after - before)
            self.assertTrue(retained <= after)
            self.assertTrue(
                all(
                    graph.degree(node) >= 1
                    for node, atom in enumerate(state)
                    if atom[0] == 3
                )
            )
            for stage in reaction["stages"]:
                if stage["after_move"] == i:
                    self.assertEqual(state, stage["atoms"])
        self.assertEqual(cuts, reaction["minimum_cuts"])
        self.assertEqual((cuts, joins, len(reaction["moves"])), (140, 140, 67))
        for stage, bonds, sites, components in zip(
            reaction["stages"],
            (315, 245, 175, 245, 315),
            (0, 140, 280, 140, 0),
            (3, 21, 43, 29, 19),
        ):
            occupancy, graph = model.inspect_open(stage["atoms"])
            self.assertEqual(model.formula(stage["atoms"]), {3: 105, 5: 42, 7: 15})
            self.assertEqual(graph.number_of_edges(), bonds)
            self.assertEqual(
                sum(len(owners) == 1 for owners in occupancy.values()), sites
            )
            self.assertEqual(nx.number_connected_components(graph), components)
        final = reaction["stages"][-1]["atoms"]
        for i, group in enumerate(reaction["product_groups"]):
            product_atoms = tuple(final[node] for node in group)
            core.analyze(product_atoms)
            self.assertEqual(
                model.formula(product_atoms), {3: 5, 5: 3} if i < 14 else {3: 7, 7: 3}
            )
        original_graph = model.inspect_open(reaction["stages"][0]["atoms"])[1]
        self.assertTrue(
            all(
                sorted(
                    reaction["stages"][0]["atoms"][j][0] for j in original_graph[node]
                )
                == [5, 5, 7]
                for node, atom in enumerate(final)
                if atom[0] == 3
            )
        )

    def test_other_shared_elements(self):
        for s, p, q in ((5, 3, 7), (7, 3, 5), (2, 3, 5)):
            with self.subTest(shared=s):
                example = model.binary_fusion(s, p, q)
                self.assertEqual(
                    model.formula(example["product"]), {s: p + q - 2, p: s, q: s}
                )
                core.analyze(example["product"])
                self.assertEqual(core.analyze(example["dimer"])[1].number_of_edges(), s)

    def test_six_cut_fusion_and_reverse(self):
        example = model.binary_fusion(3, 5, 7)
        self.assertEqual(model.formula(example["product"]), {3: 10, 5: 3, 7: 3})
        _, graph = core.analyze(example["product"])
        self.assertEqual(graph.number_of_edges(), 33)
        self.assertEqual(core.analyze(example["dimer"])[1].number_of_edges(), 3)
        sockets = []
        for fragment in example["fragments"]:
            occupancy, graph = model.inspect_open(fragment)
            self.assertTrue(nx.is_connected(graph))
            sockets.append(
                {point for point, owners in occupancy.items() if len(owners) == 1}
            )
        self.assertEqual(sockets[0], {Fraction(i, 3) for i in range(3)})
        self.assertEqual(sockets[0], sockets[1])
        for reactant, fragment in zip(example["reactants"], example["fragments"]):
            self.assertEqual(
                core.analyze(reactant)[1].number_of_edges()
                - model.inspect_open(fragment)[1].number_of_edges(),
                3,
            )
        self.assertEqual(
            Counter(p for molecule in example["reactants"] for p, _, _ in molecule),
            Counter(
                p
                for molecule in (example["product"], example["dimer"])
                for p, _, _ in molecule
            ),
        )

    def test_join_rejects_geometrically_impossible_overlap(self):
        atom = ((3, Fraction(0), None),)
        with self.assertRaisesRegex(ValueError, "overoccupied"):
            model.join((atom, atom, atom), (Fraction(0),) * 3)
        with self.assertRaisesRegex(ValueError, "overoccupied"):
            model.join((model.binary_molecule(3, 5), atom), (Fraction(0),) * 2)
        with self.assertRaisesRegex(ValueError, "partition"):
            model.fragment(atom * 2, ((0,), (0,)))
        self.assertEqual(len(model.inspect_open(())[1]), 0)

    def test_complete_parity_parameterization_by_linear_algebra(self):
        # Independently build the F2 site/line incidence matrix. Its nullity
        # must equal s+p+q-1, the number of independent coordinate bits.
        for elements in ((2, 3, 5), (3, 5, 7)):
            points = list(product(*(range(p) for p in elements)))
            lines = [
                (axis, fixed)
                for axis in range(3)
                for fixed in product(
                    *(range(p) for i, p in enumerate(elements) if i != axis)
                )
            ]
            matrix = np.array(
                [
                    [
                        tuple(x for i, x in enumerate(point) if i != axis) == fixed
                        for axis, fixed in lines
                    ]
                    for point in points
                ],
                dtype=np.uint8,
            )
            rank = 0
            for col in range(len(lines)):
                candidates = np.flatnonzero(matrix[rank:, col])
                if not len(candidates):
                    continue
                pivot = rank + candidates[0]
                matrix[[rank, pivot]] = matrix[[pivot, rank]]
                for row in range(rank + 1, len(points)):
                    if matrix[row, col]:
                        matrix[row] ^= matrix[rank]
                rank += 1
            self.assertEqual(len(lines) - rank, sum(elements) - 1)

    def test_all_357_weight_profiles_and_binary_recipes(self):
        rows = examples.weight_table()
        self.assertEqual(len(rows), 96)
        connected = [row for row in rows if row["connected_three_element"]]
        self.assertEqual(len(connected), 80)
        self.assertTrue(all(row["bipartite"] for row in rows))
        self.assertTrue(all(row["minimum_batch"] > 1 for row in connected))
        for row in rows:
            a, b, c = (row[key] for key in ("a", "b", "c"))
            self.assertEqual(row["n3"], 7 * b + 5 * c - 2 * b * c)
            self.assertEqual(row["n5"], 7 * a + 3 * c - 2 * a * c)
            self.assertEqual(row["n7"], 5 * a + 3 * b - 2 * a * b)
            self.assertEqual(
                row["minimum_batch"] * row["n3"], 5 * row["M35"] + 7 * row["M37"]
            )
            self.assertEqual(
                row["minimum_batch"] * row["n5"], 3 * row["M35"] + 7 * row["M57"]
            )
            self.assertEqual(
                row["minimum_batch"] * row["n7"], 3 * row["M37"] + 5 * row["M57"]
            )

    def test_maximum_reaction_every_intermediate(self):
        maximum = model.weight_configuration((3, 5, 7), (1, 0, 7))
        self.assertEqual(model.formula(maximum), {3: 35, 5: 14, 7: 5})
        self.assertEqual(len(set(plots.maximum_positions(maximum).values())), 54)
        self.assertEqual(
            model.batch_recipe(model.formula(maximum)),
            (3, {(3, 5): 14, (3, 7): 5, (5, 7): 0}),
        )
        path = model.atomization_path(
            (maximum,) * 3,
            (model.binary_molecule(3, 5),) * 14 + (model.binary_molecule(3, 7),) * 5,
        )
        state = list(path["initial"])
        inventory = model.formula(state)
        self.assertEqual(len(path["moves"]), 324)
        self.assertEqual(model.inspect_open(state)[1].number_of_edges(), 315)
        for i, (node, phase) in enumerate(path["moves"], 1):
            p, _, color = state[node]
            state[node] = (p, phase, color)
            occupancy, graph = model.inspect_open(state)
            self.assertEqual(model.formula(state), inventory)
            self.assertEqual(
                2 * graph.number_of_edges()
                + sum(len(owners) == 1 for owners in occupancy.values()),
                630,
            )
            if i == 162:
                self.assertEqual(graph.number_of_edges(), 0)
                self.assertEqual(tuple(state), path["isolated"])
        self.assertEqual(tuple(state), path["final"])
        occupancy, graph = model.inspect_open(state)
        self.assertTrue(all(len(owners) == 2 for owners in occupancy.values()))
        self.assertEqual(
            sorted(len(c) for c in nx.connected_components(graph)), [8] * 14 + [10] * 5
        )

    def test_maximum_with_dimer_reagent(self):
        maximum = model.weight_configuration((3, 5, 7), (1, 0, 7))
        dimer = ((5, Fraction(0), None),) * 2
        path = model.atomization_path(
            (maximum,) + (dimer,) * 7,
            (model.binary_molecule(3, 5),) * 7 + (model.binary_molecule(5, 7),),
        )
        self.assertEqual(model.formula(path["initial"]), {3: 35, 5: 28, 7: 5})
        self.assertEqual(model.formula(path["initial"]), model.formula(path["final"]))
        path = model.atomization_path(
            (model.binary_molecule(3, 5),) * 6 + (model.binary_molecule(3, 7),) * 3,
            (maximum,)
            + (((3, Fraction(0), None),) * 2,) * 8
            + (((5, Fraction(0), None),) * 2,) * 2
            + (((7, Fraction(0), None),) * 2,) * 2,
        )
        self.assertEqual(model.formula(path["initial"]), {3: 51, 5: 18, 7: 9})
        self.assertEqual(model.formula(path["initial"]), model.formula(path["final"]))


if __name__ == "__main__":
    unittest.main(verbosity=2)
