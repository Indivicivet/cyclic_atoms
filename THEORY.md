# Theory

Definitions and notation are in [INTRO.md](INTRO.md), with Lean 4 formalizations of the core definitions and selected elementary results in [`lean/`](lean/README.md). Unless stated otherwise, elements are prime, and atoms with identical point sets still count separately.

## Elementary facts

An element-$p$ atom has degree $p$ in the bond graph, counting multiple bonds. If $n_p$ is the number of $p$-atoms, then $2B = \sum_p p n_p$, where $B$ is the number of bonds. Thus the sum must be even (`two_mul_bonds_eq_sumDeg` and `even_sumDeg_of_paired` in [`lean/CyclicAtoms/Elementary.lean`](lean/CyclicAtoms/Elementary.lean)).

Two identical atoms pair every point with one another. They form a separate two-vertex molecule and cannot connect to a third atom (`identical_atoms_isolated` and `identical_atoms_molecule_only_two` in [`lean/CyclicAtoms/Elementary.lean`](lean/CyclicAtoms/Elementary.lean)).

Set $L$ to the product of the distinct prime elements. Rotate a molecule so that one of its points is at 0. Moving along a $p$-atom changes a point by a multiple of $1/p$, and moving across a bond changes nothing. Connectivity therefore places every point, and a representative phase of every atom, in $\frac{1}{L}\mathbb{Z}/\mathbb{Z}$. The Chinese remainder theorem identifies this grid with the product of coordinate groups $\mathbb{Z}_p$: a $p$-atom is a full line in the $p$ direction. A rotation translates this grid.

For distinct primes $p$ and $q$, the only molecule with element set $\{p, q\}$ has $q$ p-atoms and $p$ q-atoms, with bond graph $K_{q,p}$. A p-atom meets $p$ different q-atoms, since atoms of different prime elements meet in at most one point. Each of those q-atoms meets $q$ p-atoms, forcing the entire product grid and the complete bipartite graph. Identical atoms cannot join this molecule.

An in/out assignment exists exactly when the bond graph is bipartite. This does not imply that the graph is planar or has a physical circle-contact realisation. For example, the 23-atom construction for $\{2, 3, 5\}$ below has graph $K_{5,3}$ with every edge subdivided. It is bipartite but non-planar. Every molecule with at most three distinct prime elements is bipartite, by the parity parameterization in [CHEMISTRY.md](CHEMISTRY.md#parity-parameterization). Four or more distinct primes remains open.

## Reactions and the three-prime parity parameterization

[CHEMISTRY.md](CHEMISTRY.md) defines open configurations and atom-conserving cut/join reactions, with scripts and plots in [chemistry/](chemistry/). For three primes, every molecule using all three elements has no repeated coordinate line and is described by three coordinate bit lists, where a line is present when its two fixed coordinate bits differ. This parameterization proves bipartiteness and gives nonnegative rational binary-molecule coefficients whose denominators divide the product of the three primes. Every three-prime molecule therefore has a pure binary recipe in a batch of size dividing that product.

Under the closed-endpoint reaction model of [CLOSED_CHEMISTRY.md](CLOSED_CHEMISTRY.md) (element-conserving `1→2`, `2→1`, or `2→2` replacements between molecules, allowing molecular byproducts), any molecule using only elements from $\{3, 5, 7\}$ (one, two, or all three elements) can be formed from an initial pool containing only any two of `M35 = 3_5 5_3`, `M37 = 3_7 7_3`, and `M57 = 5_7 7_5` using `2→2` steps alone. See [UNIVERSAL_SYNTHESIS.md](UNIVERSAL_SYNTHESIS.md) and `every_molecule_with_elements357` in [`lean/CyclicAtoms/GeometricSynthesis.lean`](lean/CyclicAtoms/GeometricSynthesis.lean).

## Maximum size for three primes

### Theorem

For primes $s < p < q$, the maximum size of a molecule with element set $\{s, p, q\}$ is

$$
M(s,p,q) = pq + (s-1)q + p.
$$

### Proof sketch

For the upper bound, regard the grid as $q$ slices of size $s \times p$, and let $T$ be the number of q-atoms. In each slice there are $p$ possible s-lines and $s$ possible p-lines. If all are present they supply two incidences per point. To accommodate the $T$ q-line incidences, at least $\lceil T/p \rceil$ of these lines must be missing in each slice: each removed line frees at most $p$ incidences. This also holds when some points are unused. Thus

$$
N \le q\left(s+p-\left\lceil T/p \right\rceil\right)+T.
$$

Because $1 \le T \le sp$ and $q > p$, writing $k = \lceil T/p \rceil$ gives $T \le kp$, hence $N \le q(s+p)-k(q-p) \le q(s+p-1)+p$.

To attain the bound, put an s-line at every $(p,q)$ coordinate. Fill $s-1$ s-coordinate layers with p-lines and the last with q-lines. Each point belongs to exactly two atoms. The graph is connected: the p-lines connect p-coordinates and the q-lines connect q-coordinates, through s-lines. The formula is $s_{pq}\,p_{(s-1)q}\,q_p$. For example, `3_77 7_22 11_7` has 106 atoms. When $s=2$, the formula is $2_{pq}\,p_q\,q_p$, and the graph is $K_{q,p}$ with every edge subdivided.

The arithmetic step from the slice bound to $M(s,p,q)$ (`three_prime_upper_bound`) and the two-incidence property of the layered construction on $\mathbb{Z}_s \times \mathbb{Z}_p \times \mathbb{Z}_q$ (`three_prime_construction_twice`) are formalized in [`lean/CyclicAtoms/MaxSize.lean`](lean/CyclicAtoms/MaxSize.lean).

## Maximum size for four primes

### Theorem

For primes $s < p < q < r$, the maximum size of a molecule with element set $\{s, p, q, r\}$ is

$$
M(s,p,q,r) = pqr + (s-1)qr + (p-1)r + q.
$$

### Construction and proof idea

To attain the bound, place all s-lines, fill $s-1$ s-layers with p-lines, and in the last s-layer fill $p-1$ p-coordinate slices with q-lines and the last slice with r-lines. This gives a connected molecule with formula

$$
s_{pqr}\,p_{(s-1)qr}\,q_{(p-1)r}\,r_q
$$

in which every grid point has two incidences.

For the upper bound, group the grid into $qr$ slices of size $s \times p$ by $(q,r)$ coordinates. In each slice $(y,z)$, incidence counting bounds the missing $(s,p)$-lines by $p d_{y,z} \ge Q_z + R_y$, while connectivity forces $d_{y,z} \ge 1$. Summing down each r-column $z$ and comparing the total r-atom count $R$ against $q$ shows that the slice-incidence relaxation is already bounded by $M(s,p,q,r)$. See [PROOF_SKETCHES.md](PROOF_SKETCHES.md) for the full proof sketch and [`lean/CyclicAtoms/MaxSize.lean`](lean/CyclicAtoms/MaxSize.lean) for the Lean 4 formalization (`four_prime_upper_bound`, `four_prime_upper_bound_of_columns`, and `four_prime_construction_twice`).

For $\{3, 5, 7, 11\}$ the maximum construction gives `3_385 5_154 7_44 11_7`, with 590 atoms (`verification/verify_max_35711.py`). For comparison, the symmetric three-layer product `3_385 5_77 7_55 11_35` has 552 atoms, and a mixed example `3_385 5_143 7_55 11_5` has 588. Thus the symmetric product is not always maximal.

## Enumeration and speculative questions

An earlier search reported 35 molecules with element set $\{2, 3, 5\}$ up to rotation, and also 35 up to rotation and reflection; all 35 were bipartite. The original enumeration script is not available in this package, so this result has not been reproduced here. The same applies to the report that the 23-atom maximum is unique up to rotation.

Earlier MILP runs reported matching lower and upper bounds for $(2,3,5,7):159$, $(2,3,5,11):247$, $(2,3,7,11):337$, $(2,5,7,13):605$, $(3,5,7,11):590$, $(3,5,7,13):696$, $(3,5,11,13):1064$, $(3,7,11,13):1376$, and $(5,7,11,13):1662$, all of which agree with $M(s,p,q,r)$ above (which also gives $908$ for $(3,5,7,17)$ and $2104$ for $(3,7,13,17)$).

A broader speculation is that for every finite set of at least two distinct primes there is a maximum molecule occupying every grid point twice, with all smallest-element atoms on one side of a bipartition and the other atoms on the other side. This remains open for five or more primes. Other questions are whether every molecule is bipartite, how to classify maxima and symmetries, what changes for composite elements, and which graphs admit physical geometric realisations.

### General $n$-prime bounds and conjecture

For any finite collection of $n \ge 2$ distinct primes $p_1 < p_2 < \dots < p_n$, the layered construction generalizes directly:
1. Place all $p_1$-lines, giving $N_1 = \prod_{i=2}^n p_i = P / p_1$ atoms.
2. For each $k \in \{2, \dots, n-1\}$, fill $p_{k-1} - 1$ layers of coordinate $x_{k-1}$ with $p_k$-lines, giving $N_k = (p_{k-1} - 1) \prod_{i=k+1}^n p_i$ atoms.
3. In the final $p_{n-1} \times p_n$ subspace, place $N_n = p_{n-1}$ lines of type $p_n$.

Because the incidence sum telescopes,
$$
\sum_{k=1}^n p_k N_k = P + \sum_{k=2}^{n-1} \left(\prod_{i=k-1}^n p_i - \prod_{i=k}^n p_i\right) + p_{n-1} p_n = 2P,
$$
every point of the grid $\prod_{i=1}^n \mathbb{Z}_{p_i}$ is incident to exactly two atoms. The bond graph is bipartite (with all $p_1$-atoms on one side) and connected via the $p_1$-lines. This establishes an explicit **lower bound** for all $n \ge 2$:

$$
M(p_1, \dots, p_n) \ge \prod_{i=2}^n p_i + \sum_{k=2}^{n-1} (p_{k-1} - 1) \prod_{i=k+1}^n p_i + p_{n-1}.
$$

Equivalently, this bound satisfies the recurrence:

$$
M(p_1, \dots, p_n) \ge p_n \bigl(M(p_1, \dots, p_{n-1}) - 1\bigr) + p_{n-1}, \quad M(p_1, p_2) = p_1 + p_2.
$$

**Conjecture (General Upper Bound):** The layered construction achieves the maximum possible size for any $n$ distinct primes:

$$
M(p_1, \dots, p_n) = \prod_{i=2}^n p_i + \sum_{k=2}^{n-1} (p_{k-1} - 1) \prod_{i=k+1}^n p_i + p_{n-1} = p_n \bigl(M(p_1, \dots, p_{n-1}) - 1\bigr) + p_{n-1}.
$$

This is proven for $n=2$ (uniqueness of $K_{q,p}$), $n=3$ ($M(s,p,q)$), and $n=4$ ($M(s,p,q,r)$), and supported by MILP relaxations across all tested parameter regimes, but remains open for $n \ge 5$.
