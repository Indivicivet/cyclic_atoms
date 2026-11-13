# Cyclic atoms

A cyclic atom is a collection of equally spaced points on a circle. A molecule is a connected collection of atoms whose points pair up exactly. This project studies which molecules exist, how large they can be, and how to draw them.

## Basic definitions

[Atom] An **atom** $(p, a)$ has element $p \ge 2$ and phase $a$ in turns. Its points are $a + k/p \pmod 1$, for $k = 0, \ldots, p-1$. Phases differing by a multiple of $1/p$ describe the same point set. We typically take atoms to require $p$ to be prime, as suggested by the notation, but may consider "non-prime" atoms as a generalization.

[Configuration] A **configuration** is a finite multiset of atoms. We consider configurations equivalent up to rotation, but not reflection. Configurations that are not equivalent to their reflection are called *chiral*.

[Bond graph] The **bond graph** (or just "graph") of a configuration has one vertex per atom and one edge per bond. Multiple bonds between the same atoms are separate edges.

[Molecule] A **molecule** is a *connected* configuration such that every point is on exactly two atoms. By connected, we mean that the bond graph is connected as a graph.

[Element set] An **element set** is the set of distinct atom elements present. This will often be denoted as a normal set of integers, e.g. $\{2, 3\}$, $\{3, 5\}$, $\{2, 5, 7, 11\}$.

[Chemical formula] The **chemical formula** (or just "formula") records the multiplicities of each element in a configuration, for example `2_15 3_5 5_3` has 23 atoms.

[Size] The **size** of a configuration is the total number of *atoms*.

Unless stated otherwise, our results concern distinct prime elements. Non-prime (composite) elements may be allowed but will be stated explicitly.

A graph colouring with opposite colours at every bond is called an **in/out assignment**. It exists exactly when the bond graph is bipartite.

## Chemistry

In an *open configuration*, occupied points belong to either one or two atoms. A point on just one atom is an *open site*. A *closed configuration* has every occupied point paired; its connected components are molecules. A *fragment* is a group of intact atoms kept together during a reaction, possibly with open sites.

We can cut a configuration into separately rotatable fragments and join fragments when their open sites coincide, provided total occupancy never exceeds two. Atoms remain intact, so element counts are conserved. [CHEMISTRY.md](CHEMISTRY.md) covers these reaction rules, proves that every three-prime molecule can be assembled from two-element molecules in some finite batch, and works out the minimum 140-cut split of three `3_35 5_14 7_5` molecules into fourteen `3_5 5_3` and five `3_7 7_3` molecules.

The atom, configuration, and molecule definitions are formalized in Lean 4 in [`lean/CyclicAtoms/Defs.lean`](lean/CyclicAtoms/Defs.lean) (see [`lean/README.md`](lean/README.md)).

If every intermediate must consist entirely of molecules, the three-copy split cannot be composed from reactions with at most two inputs and two outputs, starting with only maxima. [CLOSED_CHEMISTRY.md](CLOSED_CHEMISTRY.md) gives the obstruction and the possible small closed reaction formulas.

With molecular byproducts allowed, any two of M35, M37 and M57 suffice to
synthesize any 3-5-7 molecule, using only 2→2 closed-endpoint reactions.
[UNIVERSAL_SYNTHESIS.md](UNIVERSAL_SYNTHESIS.md) gives the proof, explicit finite
recipes for every target, and an end-to-end Lean proof starting from the
original `IsMolecule` definition. [The proof audit](lean/PROOF_AUDIT.md) gives
the exact theorem statement and the meaning of its reaction rules.

## Basic examples

Two identical atoms $(2, 0), (2, 0)$ form a molecule with two vertices joined by two bonds. The atoms are distinct even though their points coincide.

Note that any two identical atoms $(p, 0), (p, 0)$ can form a molecule, but these identical atoms cannot be part of any larger molecule, since all nodes are already connected. Of course, two identical *elements* can form a larger molecule with other elements.

For distinct primes $p, q$, the connected two-element molecule is unique up to rotation: it has $q$ atoms of element $p$ and $p$ of element $q$; its graph is $K_{q,p}$. e.g. the following is *the* $\{2, 5\}$ molecule: two 5-atoms and five 2-atoms.

A non-prime example is $[(2, 0), (2, 1/4), (4, 0)]$: the two 2-atoms split the four points of the 4-atom. We will not consider this part of "default" discourse.

## Atom notation

### Notation 0A

Notation 0A is a list of tuples (or length 2 lists), each one consisting of a cyclic group length and an offset in turns, as used by [humanity/cp_pair_diagrams.py](humanity/cp_pair_diagrams.py), e.g.

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

