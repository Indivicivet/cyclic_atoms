# A non-bipartite molecule

Not every prime-element molecule has a bipartite bond graph. The construction
below has formula `2_19 3_6 5_4 7_4`, with 33 atoms and 52 bonds, and contains a
7-cycle. Every occupied point belongs to exactly two atoms, and the graph is
connected. No claim is made that 33 is the smallest possible atom count.

## Construction

Work in the CRT grid

$$
G=\mathbb Z_3\times\mathbb Z_5\times\mathbb Z_7\times\mathbb Z_2,
$$

with coordinates `(x, y, z, t)`. A full coordinate line is an atom whose
element is the size of its varying coordinate. A star below means that the
coordinate ranges over its whole group.

For each `t = 0, 1`, include these seven atoms, in the order shown:

| Atom | x | y | z | t | Element |
|---|---|---|---|---|---|
| A_t | * | 0 | 0 | t | 3 |
| B_t | 1 | * | 0 | t | 5 |
| C_t | * | 1 | 0 | t | 3 |
| D_t | 2 | 1 | * | t | 7 |
| E_t | * | 1 | 1 | t | 3 |
| F_t | 0 | * | 1 | t | 5 |
| H_t | 0 | 0 | * | t | 7 |

Let `m(x,y,z)` count the seven base lines through `(x,y,z)`, ignoring `t`.
For every triple with `m(x,y,z) = 1`, include the 2-atom

$$
\{(x,y,z,0),(x,y,z,1)\}.
$$

There are exactly 19 such triples. Include no other atoms.

## Proof of validity and non-bipartiteness

Within either layer, the seven lines have exactly the following intersections:

| Pair | Intersection `(x,y,z)` |
|---|---|
| A_t, B_t | (1, 0, 0) |
| B_t, C_t | (1, 1, 0) |
| C_t, D_t | (2, 1, 0) |
| D_t, E_t | (2, 1, 1) |
| E_t, F_t | (0, 1, 1) |
| F_t, H_t | (0, 0, 1) |
| H_t, A_t | (0, 0, 0) |

Every other pair is disjoint: parallel lines have different fixed coordinates,
and every nonconsecutive pair of different directions has conflicting fixed
coordinates. The seven displayed intersection points are distinct. In
particular, `m` takes only the values 0, 1, and 2.

At a point with `m = 2`, the two layer atoms already pair it and no 2-atom is
added. At a point with `m = 1`, exactly one 2-atom is added, pairing its site in
each layer. At a point with `m = 0`, no atom is present. Thus every occupied
point has occupancy exactly two.

The seven atoms in each layer form a cycle. Each added 2-atom joins one layer
atom to its copy in the other layer. Since there are such atoms, the whole
graph is connected. It is therefore a molecule under the project's definition.

The bonds

$$
A_0-B_0-C_0-D_0-E_0-F_0-H_0-A_0
$$

form a 7-cycle, proving that the bond graph is not bipartite.

## Counts and circle phases

The seven base lines have total incidence

$$
3+5+3+7+3+5+7=33.
$$

Seven points are double, so there are `33 - 2*7 = 19` single points.
Two layers contribute six 3-atoms, four 5-atoms, and four 7-atoms. Adding the
nineteen 2-atoms gives 33 atoms in total. The degree sum gives

$$
B=\frac{19\cdot2+6\cdot3+4\cdot5+4\cdot7}{2}=52.
$$

To realize the construction on the original circle, send a grid point to

$$
\theta(x,y,z,t)
=\frac{70x+126y+120z+105t}{210}\pmod1.
$$

The coefficients are the CRT idempotents modulo `(3,5,7,2)`. Varying one
coordinate therefore gives exactly one equally spaced prime-element atom.
This proves that the grid construction is a cyclic-atom molecule, rather
than merely an abstract incidence pattern.

The exact circle phases of all 33 atoms are in
[nonbipartite_2357.json](verification/nonbipartite_2357.json), in 0A notation.
The first seven atoms are the displayed cycle in layer zero. Their bond phases,
in cyclic order, are

$$
\frac13,\quad \frac{14}{15},\quad \frac4{15},\quad
\frac{88}{105},\quad \frac6{35},\quad \frac47,\quad 0.
$$

The [exact verifier](verification/check_bipartiteness_counterexample.py)
constructs these atoms, checks circle-point occupancy using rational arithmetic,
checks connectivity and the seven cycle edges, and verifies the exported JSON:

```sh
python -m verification.check_bipartiteness_counterexample
```

Together with the [three-prime bipartiteness proof](CHEMISTRY.md#bipartiteness),
this shows that four is the smallest number of distinct prime elements that
can support a non-bipartite molecule.

## General closing construction

The same method closes any connected open configuration of coordinate lines
whose occupied points have multiplicity one or two. Choose a new prime `r`,
make `r` copies in a new coordinate, and insert an `r`-line at every base point
of multiplicity one. Every occupied point then has multiplicity two. If the
base configuration has an open site, these new lines connect all copies;
if it has an odd cycle, that cycle survives in each copy.
