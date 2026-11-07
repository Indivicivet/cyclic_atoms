# Cyclic atoms

A cyclic atom is a collection of equally spaced points on a circle. A molecule is a connected collection of atoms whose points pair up exactly. This project studies which molecules exist, how large they can be, and how to draw them.

## Basic definitions

- The **circle** is the set of turns modulo 1, written R/Z. One turn is a full revolution.
- An **atom** `(n, a)` has element `n ≥ 2` and phase `a` in turns. Its points are `a + k/n (mod 1)`, for `k = 0, …, n−1`. Phases differing by a multiple of `1/n` describe the same point set.
- A **configuration** is a finite multiset of atoms: two identical atoms still count as two. It is **valid** if every point is on either zero or exactly two atoms. A point shared by two atoms is a **bond**.
- The **bond graph** has one vertex per atom and one edge per bond. Multiple bonds between the same atoms are separate edges. A **molecule** is a nonempty valid configuration whose bond graph is connected. A valid configuration can be a disjoint union of molecules.
- An **element set** is the set of distinct atom elements present; the **formula** records their multiplicities, for example `2_15 3_5 5_3` has 23 atoms. The **size** is the total number of atoms, not the number of bonds.

Unless stated otherwise, our results concern distinct prime elements. Composite elements are allowed by the definitions. Absolute phase is meaningful in a representation, but comparisons *up to rotation* identify configurations obtained by adding the same phase to every atom; reflection sends `a` to `−a`. A rotated molecule remains the same up to rotation, not necessarily as a literal list.

A graph colouring with opposite colours at every bond is called an **in/out assignment**. It exists exactly when the bond graph is bipartite. It is a combinatorial convention: it does not guarantee that rigid circles can be arranged in the plane with physically touching spikes.

## Basic examples

Two identical atoms `(2, 0), (2, 0)` form a molecule with two vertices joined by two bonds. The atoms are distinct even though their points coincide.

For distinct primes `p, q`, the connected two-element molecule is unique up to rotation: it has `q` atoms of element `p` and `p` of element `q`; its graph is `K_(q,p)`. In particular, the following is the 2–5 molecule: two 5-atoms and five 2-atoms.

A non-prime example is `[(2, 0), (2, 1/4), (4, 0)]`: the two 2-atoms split the four points of the 4-atom. It also illustrates why the general definition does not require primality.

## Atom notation

### Notation 0A

Notation 0A is a list of tuples (or length 2 lists), each one consisting of a cyclic group length and an offset in turns, as used by humanity/cp_pair_diagrams.py, e.g.

[2, 0], [2, 1 / 4], [4, 0]  # 4 isn't prime but it's an easy example

or

[5, 0],
[5, 1 / 10],
*[[2, i / 10] for i in range(5)]

which represents the unique connected molecule with atom set {2, 5}

### Notation 0B

Notation 0B is a python dict[tuple[list[int], list[int]]] where the dict keys represent the base cyclic group length (prime p) and the two lists are the "outward facing" and "inward facing" indices of the identity of the group, where numbers go from {0, ..., p1p2p3...pn - 1}, where p_i are all of the primes, e.g.

3: [[35,70,105,140,175,210,245,280,315,350],[77,154,231,308]]
5: [[77,154],[33,66,99,132,165,198]]
7: [[0,33,66,99,132],[]]
11: [[],[0,35,70]]

in this case the numbers go from 0 to 3*5*7*11 - 1.

