# Theory

Definitions and notation are in [INTRO.md](INTRO.md), with Lean 4 formalizations of the core definitions and selected elementary results in [`lean/`](lean/README.md). Unless stated otherwise, elements are prime, and atoms with identical point sets still count separately.

## Elementary facts

An element-$p$ atom has degree $p$ in the bond graph, counting multiple bonds. If $n_p$ is the number of $p$-atoms, then $2B = \sum_p p n_p$, where $B$ is the number of bonds. Thus the sum must be even (`two_mul_bonds_eq_sumDeg` and `even_sumDeg_of_paired` in [`lean/CyclicAtoms/Theory.lean`](lean/CyclicAtoms/Theory.lean)).

Two identical atoms pair every point with one another. They form a separate two-vertex molecule and cannot connect to a third atom (`identical_atoms_isolated` and `identical_atoms_molecule_only_two` in [`lean/CyclicAtoms/Theory.lean`](lean/CyclicAtoms/Theory.lean)).

Set $L$ to the product of the distinct prime elements. Rotate a molecule so that one of its points is at 0. Moving along a $p$-atom changes a point by a multiple of $1/p$, and moving across a bond changes nothing. Connectivity therefore places every point, and a representative phase of every atom, in $\frac{1}{L}\mathbb{Z}/\mathbb{Z}$. The Chinese remainder theorem identifies this grid with the product of coordinate groups $\mathbb{Z}_p$: a $p$-atom is a full line in the $p$ direction. A rotation translates this grid.

For distinct primes $p$ and $q$, the only molecule with element set $\{p, q\}$ has $q$ p-atoms and $p$ q-atoms, with bond graph $K_{q,p}$. A p-atom meets $p$ different q-atoms, since atoms of different prime elements meet in at most one point. Each of those q-atoms meets $q$ p-atoms, forcing the entire product grid and the complete bipartite graph. Identical atoms cannot join this molecule.

An in/out assignment exists exactly when the bond graph is bipartite. This does not imply that the graph is planar or has a physical circle-contact realisation. For example, the 23-atom construction for $\{2, 3, 5\}$ below has graph $K_{5,3}$ with every edge subdivided. It is bipartite but non-planar. Whether every prime-element molecule is bipartite remains open here.

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

The arithmetic step from the slice bound to $M(s,p,q)$ (`three_prime_upper_bound`) and the two-incidence property of the layered construction on $\mathbb{Z}_s \times \mathbb{Z}_p \times \mathbb{Z}_q$ (`three_prime_construction_twice`) are formalized in [`lean/CyclicAtoms/Theory.lean`](lean/CyclicAtoms/Theory.lean).

## Maximum size for four primes

### Theorem

For primes $s < p < q < r$, the maximum size of a molecule with element set $\{s, p, q, r\}$ is

$$
M(s,p,q,r) = pqr + (s-1)qr + (p-1)r + q.
$$

### Proof sketch

Group the $spqr$ grid sites by their $(q,r)$ coordinates $(y,z) \in \mathbb{Z}_q \times \mathbb{Z}_r$ into $qr$ slices of size $s \times p$. In slice $(y,z)$, let $a_{y,z}$ be the number of absent s-lines among $p$ possible ones, $b_{y,z}$ the number of absent p-lines among $s$, $d_{y,z} = a_{y,z} + b_{y,z}$ the total number of absent $(s,p)$-lines, $Q_z$ the number of q-lines at $r$-coordinate $z$, $R_y$ the number of r-lines at $q$-coordinate $y$, and $e_{y,z}$ the number of empty sites. Counting incidences in slice $(y,z)$ gives

$$
s a_{y,z} + p b_{y,z} = Q_z + R_y + 2e_{y,z}.
$$

Because $s < p$ and $e_{y,z} \ge 0$, every slice satisfies $Q_z + R_y \le p d_{y,z}$. Every slice also satisfies $d_{y,z} \ge 1$. If $Q_z + R_y > 0$, then $p d_{y,z} \ge Q_z + R_y \ge 1$ forces $d_{y,z} \ge 1$. If $Q_z + R_y = 0$, no q-line or r-line meets slice $(y,z)$. Since s-lines and p-lines stay inside the slice and the connected molecule contains q- and r-atoms, the slice must be empty, giving $d_{y,z} = s + p \ge 1$.

Let $Q = \sum_{z \in \mathbb{Z}_r} Q_z \ge 1$ and $R = \sum_{y \in \mathbb{Z}_q} R_y \ge 1$ be the total numbers of q-atoms and r-atoms, and set $D_z = \sum_{y \in \mathbb{Z}_q} d_{y,z}$ and $D = \sum_{z \in \mathbb{Z}_r} D_z$. The molecule has size

$$
N = qr(s+p) - D + Q + R.
$$

In each column $z \in \mathbb{Z}_r$, summing $d_{y,z} \ge 1$ and $Q_z + R_y \le p d_{y,z}$ over $y \in \mathbb{Z}_q$ gives $D_z \ge q$ and $q Q_z + R \le p D_z$. Adding $(q-p)q \le (q-p)D_z$ yields

$$
q(Q_z + q - p) + R \le q D_z.
$$

There are two cases depending on how $R$ compares to $q$:

1. If $R \le q$, then $R \ge 1$ gives $q(Q_z + q - p) + 1 \le q D_z$, so $Q_z + q - p + 1 \le D_z$ for every $z$. Summing over all $r$ columns gives $Q + r(q - p + 1) \le D$, and adding $R \le q$ yields $Q + R + qr \le D + (p-1)r + q$.
2. If $R \ge q$, summing $q(Q_z + q - p) + R \le q D_z$ over all $r$ columns gives $q Q + r R + qr(q - p) \le q D$. Since $r \ge q$ and $R \ge q$, we have $(r - q)(R - q) \ge 0$, or $r R \ge q R + q(r - q)$. Substituting this lower bound for $r R$ and dividing by $q$ again yields $Q + R + qr \le D + (p-1)r + q$.

In both cases $Q + R - D \le (p-1)r + q - qr$, so

$$
N = qr(s+p) - D + Q + R \le qr(s+p-1) + (p-1)r + q = pqr + (s-1)qr + (p-1)r + q.
$$

To attain the bound, place all s-lines, fill $s-1$ s-layers with p-lines, and in the last s-layer fill $p-1$ p-coordinate slices with q-lines and the last slice with r-lines. This gives a connected molecule with formula

$$
s_{pqr}\,p_{(s-1)qr}\,q_{(p-1)r}\,r_q
$$

in which every grid point has two incidences.

The slice bound (`four_prime_slice_bound`), single-column step (`four_prime_column_bound`), column aggregation (`validColumns_aggregate`), deficit bound (`four_prime_deficit_bound`), upper bound (`four_prime_upper_bound` and `four_prime_upper_bound_of_columns`), and two-incidence property of the layered construction on $\mathbb{Z}_s \times \mathbb{Z}_p \times \mathbb{Z}_q \times \mathbb{Z}_r$ (`four_prime_construction_twice`) are formalized in [`lean/CyclicAtoms/Theory.lean`](lean/CyclicAtoms/Theory.lean).

### Examples for $\{3, 5, 7, 11\}$

For $\{3, 5, 7, 11\}$ the maximum construction gives `3_385 5_154 7_44 11_7`, with 590 atoms. The script `verification/verify_max_35711.py` checks this construction and solves the corresponding slice-incidence MILP relaxation on the 77 groups of size $3 \times 5$. For comparison, the symmetric three-layer product `3_385 5_77 7_55 11_35` has 552 atoms, and a mixed example `3_385 5_143 7_55 11_5` has 588. Thus the symmetric product is not always maximal.

## Enumeration and speculative questions

An earlier search reported 35 molecules with element set $\{2, 3, 5\}$ up to rotation, and also 35 up to rotation and reflection; all 35 were bipartite. The original enumeration script is not available in this package, so this result has not been reproduced here. The same applies to the report that the 23-atom maximum is unique up to rotation.

Earlier MILP runs reported matching lower and upper bounds for $(2,3,5,7):159$, $(2,3,5,11):247$, $(2,3,7,11):337$, $(2,5,7,13):605$, $(3,5,7,11):590$, $(3,5,7,13):696$, $(3,5,11,13):1064$, $(3,7,11,13):1376$, and $(5,7,11,13):1662$, all of which agree with $M(s,p,q,r)$ above (which also gives $908$ for $(3,5,7,17)$ and $2104$ for $(3,7,13,17)$).

A broader speculation is that for every finite set of at least two distinct primes there is a maximum molecule occupying every grid point twice, with all smallest-element atoms on one side of a bipartition and the other atoms on the other side. This remains open for five or more primes. Other questions are whether every molecule is bipartite, how to classify maxima and symmetries, what changes for composite elements, and which graphs admit physical geometric realisations.
