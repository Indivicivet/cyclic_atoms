"""Open configurations, exact joining, and three-prime stoichiometry.

Atoms use the existing visualization.core format: (element, Fraction phase, color).
Reaction paths are discrete rotations of intact atoms; no continuous dynamics or
energy model is assumed. Run examples with ``python -m chemistry.examples``.
"""

from collections import Counter, defaultdict, deque
from fractions import Fraction
from itertools import product
from math import isqrt, lcm, prod

import networkx as nx

import visualization.core as core


def inspect_open(atoms):
    """Return occupancy and bond multigraph, allowing unpaired sites and emptiness."""
    occupancy = defaultdict(list)
    graph = nx.MultiGraph()
    graph.add_nodes_from(range(len(atoms)))
    for i, atom in enumerate(atoms):
        for point in core.sites(atom):
            occupancy[point].append(i)
    for point, owners in occupancy.items():
        if len(owners) > 2:
            raise ValueError(f"overoccupied site {point}: {owners}")
        if len(owners) == 2:
            i, j = owners
            if atoms[i][2] is not None and atoms[i][2] == atoms[j][2]:
                raise ValueError(f"same-color bond at {point}")
            graph.add_edge(i, j, phase=point)
    return dict(occupancy), graph


def rotate(atoms, turns):
    return tuple((p, (phase + turns) % Fraction(1, p), c) for p, phase, c in atoms)


def join(fragments, rotations):
    """Rotate each fragment rigidly, then join exactly the coincident open sites.

    An overlap with an already paired site is an error, even if the resulting
    abstract graph would have the desired degrees.
    """
    if len(fragments) != len(rotations):
        raise ValueError("one rotation is required per fragment")
    atoms = tuple(
        atom
        for fragment, turns in zip(fragments, rotations)
        for atom in rotate(fragment, turns)
    )
    inspect_open(atoms)
    return atoms


def fragment(atoms, groups):
    """Partition intact atoms into separate frames, exposing all crossing bonds.

    These fragments are separate configurations until passed to join. Merely
    erasing an edge while leaving coincident atoms in one frame is not a cut.
    """
    if any(not group for group in groups) or sorted(
        i for group in groups for i in group
    ) != list(range(len(atoms))):
        raise ValueError("groups must partition all atom indices exactly once")
    inspect_open(atoms)
    return tuple(tuple(atoms[i] for i in group) for group in groups)


def formula(atoms):
    return dict(sorted(Counter(p for p, _, _ in atoms).items()))


def binary_molecule(p, q):
    if p == q or any(
        n < 2 or any(n % d == 0 for d in range(2, isqrt(n) + 1)) for n in (p, q)
    ):
        raise ValueError("binary molecules here require two distinct primes")
    return tuple(
        (element, Fraction(i, p * q), None)
        for element, count in ((p, q), (q, p))
        for i in range(count)
    )


def parity_configuration(elements, bits):
    """Use three coordinate bit lists to select all lines crossing the bit cut.

    A p-line is present exactly when its two fixed coordinate bits differ.
    The CRT uses residues of the integer circle-grid index, matching THEORY.md.
    """
    if (
        len(elements) != 3
        or len(set(elements)) != 3
        or any(
            p < 2 or any(p % d == 0 for d in range(2, isqrt(p) + 1)) for p in elements
        )
    ):
        raise ValueError("three distinct primes are required")
    if len(bits) != 3 or any(
        len(values) != p or any(v not in (0, 1) for v in values)
        for p, values in zip(elements, bits)
    ):
        raise ValueError("one binary list of length p is required per prime")
    grid = prod(elements)
    weights = [grid // p * pow(grid // p, -1, p) for p in elements]
    atoms = []
    for axis, p in enumerate(elements):
        others = [i for i in range(3) if i != axis]
        for fixed in product(*(range(elements[i]) for i in others)):
            if bits[others[0]][fixed[0]] != bits[others[1]][fixed[1]]:
                index = sum(weights[i] * x for i, x in zip(others, fixed)) % grid
                atoms.append((p, Fraction(index, grid) % Fraction(1, p), None))
    return tuple(atoms)


def weight_configuration(elements, weights):
    return parity_configuration(
        elements,
        tuple(tuple(int(i < k) for i in range(p)) for p, k in zip(elements, weights)),
    )


def binary_requirements(counts, elements=(3, 5, 7)):
    """Exact rational binary counts; a reaction needs nonnegative integers."""
    s, p, q = elements
    ns, np, nq = (counts.get(element, 0) for element in elements)
    return {
        (s, p): Fraction(s * ns + p * np - q * nq, 2 * s * p),
        (s, q): Fraction(s * ns - p * np + q * nq, 2 * s * q),
        (p, q): Fraction(-s * ns + p * np + q * nq, 2 * p * q),
    }


def batch_recipe(counts, elements=(3, 5, 7)):
    requirements = binary_requirements(counts, elements)
    if any(value < 0 for value in requirements.values()):
        raise ValueError("no positive batch can be made from only binary molecules")
    batch = lcm(*(value.denominator for value in requirements.values()))
    return batch, {pair: int(batch * value) for pair, value in requirements.items()}


def atomization_path(reactants, products):
    """Construct an exact collision-free discrete path with stable atom indices.

    All reactant, product and free-atom frames receive distinct cosets of a
    common rational grid. Remove atoms into private frames, then place them in
    the product frames. Every intermediate occupancy is at most two. This is a
    deliberately permissive existence construction, not a low-cut mechanism.
    """
    for molecule in (*reactants, *products):
        core.analyze(molecule)
        if any(color is not None for _, _, color in molecule):
            raise ValueError("reaction paths require unsigned atoms")
    inventory = Counter(p for molecule in reactants for p, _, _ in molecule)
    if inventory != Counter(p for molecule in products for p, _, _ in molecule):
        raise ValueError("reaction does not conserve each element")
    grid = lcm(
        *(
            denominator
            for molecule in (*reactants, *products)
            for p, phase, _ in molecule
            for denominator in (p, phase.denominator)
        )
    )
    frames = len(reactants) + len(products)
    spacing = Fraction(1, grid * (frames + sum(inventory.values()) + 1))
    initial = tuple(
        atom
        for i, molecule in enumerate(reactants, 1)
        for atom in rotate(molecule, i * spacing)
    )
    destinations = defaultdict(deque)
    for i, molecule in enumerate(products, len(reactants) + 1):
        for p, phase, _ in rotate(molecule, i * spacing):
            destinations[p].append(phase)
    isolated = tuple(
        (p, (frames + i) * spacing, None) for i, (p, _, _) in enumerate(initial, 1)
    )
    final = tuple((p, destinations[p].popleft(), None) for p, _, _ in initial)
    return {
        "initial": initial,
        "isolated": isolated,
        "final": final,
        "moves": tuple(
            (i, phase)
            for state in (isolated, final)
            for i, (_, phase, _) in enumerate(state)
        ),
    }


def binary_fusion(s, p, q):
    """M(s,p) + M(s,q) -> T + D(s), cutting the two selected s-atoms out."""
    if p == q:
        raise ValueError("fusion requires three distinct primes")
    left = binary_molecule(s, p)
    right = binary_molecule(s, q)
    left_root = next(
        i for i, (element, phase, _) in enumerate(left) if element == s and phase == 0
    )
    right_root = next(
        i for i, (element, phase, _) in enumerate(right) if element == s and phase == 0
    )
    left_parts = fragment(
        left, ((left_root,), tuple(i for i in range(len(left)) if i != left_root))
    )
    right_parts = fragment(
        right, ((right_root,), tuple(i for i in range(len(right)) if i != right_root))
    )
    return {
        "reactants": (left, right),
        "fragments": (left_parts[1], right_parts[1]),
        "product": join((left_parts[1], right_parts[1]), (Fraction(0), Fraction(0))),
        "dimer": join((left_parts[0], right_parts[0]), (Fraction(0), Fraction(0))),
        "roots": (left_root, right_root),
    }
