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

## Constructions for four primes

For $s < p < q < r$, there is a connected construction with formula

$$
s_{pqr}\,p_{(s-1)qr}\,q_{(p-1)r}\,r_q
$$

and size $pqr + (s-1)qr + (p-1)r + q$. Place all s-lines; fill $s-1$ s-layers with p-lines, then in the last layer fill $p-1$ p-coordinate slices with q-lines and the last slice with r-lines. Every grid point has exactly two incidences and the graph is connected.

We conjecture that this construction is maximum for all four distinct primes.

For $\{3, 5, 7, 11\}$ it gives `3_385 5_154 7_44 11_7`, with 590 atoms. The integer optimisation in `verification/verify_max_35711.py` gives an upper bound of 590 for a relaxation of the connected problem. It uses floating-point MILP, so the result is subject to solver tolerances and is not a solver-independent proof certificate. The script also checks the construction.

### The 590 upper-bound relaxation

Group the 1155 grid sites by their $(7,11)$ coordinates into 77 grids of size $3 \times 5$. In group $(y,z)$, let $a$ be the number of absent 3-lines among five possible ones, $b$ the number of absent 5-lines among three, $Q_z$ the number of 7-lines at that 11-coordinate, $R_y$ the number of 11-lines at that 7-coordinate, and $e$ the number of empty sites. Counting incidences gives $3a+5b=Q_z+R_y+2e$. Connectivity implies that a group with $Q_z+R_y=0$ must be empty, since no larger line can join it to another group. The MILP maximises the number of lines subject to these necessary constraints and the existence of both 7- and 11-atoms. It does not require the local counts to arise from a consistent physical arrangement, so it is an upper-bound relaxation. The supplied script obtains bound 590 and checks a construction attaining it.

For comparison, the symmetric three-layer product `3_385 5_77 7_55 11_35` has 552 atoms. A mixed example `3_385 5_143 7_55 11_5` has 588. Thus the symmetric product is not always maximal.

## Enumeration and speculative questions

An earlier search reported 35 molecules with element set $\{2, 3, 5\}$ up to rotation, and also 35 up to rotation and reflection; all 35 were bipartite. The original enumeration script is not available in this package, so this result has not been reproduced here. The same applies to the report that the 23-atom maximum is unique up to rotation.

Earlier MILP runs reported matching lower and upper bounds for $(2,3,5,7):159$, $(2,3,5,11):247$, $(2,3,7,11):337$, $(2,5,7,13):605$, $(3,5,7,11):590$, $(3,5,7,13):696$, $(3,5,11,13):1064$, $(3,7,11,13):1376$, and $(5,7,11,13):1662$. Only the 3,5,7,11 verification is included here; the others remain unreproduced reports. Runs for $(3,5,7,17)$ and $(3,7,13,17)$ did not close the gap.

A broader speculation is that for every finite set of at least two distinct primes there is a maximum molecule occupying every grid point twice, with all smallest-element atoms on one side of a bipartition and the other atoms on the other side. This has been less tested than the four-prime conjecture. Other questions are whether every molecule is bipartite, how to classify maxima and symmetries, what changes for composite elements, and which graphs admit physical geometric realisations.
