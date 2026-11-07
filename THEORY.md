# Theory

Definitions, conventions and notation are in [INTRO.md](INTRO.md). Unless otherwise stated, elements are primes. Counts identify atoms even if their point sets coincide. Claims are separated by strength below.

## Elementary facts

**Degree and incidences.** An element-`p` atom has degree `p` in the bond multigraph, counting parallel edges. If `n_p` is its multiplicity, then `2B = Σ p n_p`, where `B` is the number of bonds. Thus the sum must be even.

**Equal atoms.** Two identical atoms pair every point with one another. They form a separate two-vertex molecule and cannot connect to a third atom.

**Finite grid.** Set `L` to the product of the distinct prime elements. Fix a point of one atom at 0. Moving along an atom changes a point by an integer multiple of `1/p`, and moving across a bond changes nothing. Connectivity therefore places every point, and a representative phase of every atom, in `(1/L) Z/Z`. The Chinese remainder theorem identifies this grid with the product of coordinate groups `Z_p`: a `p`-atom is a full line in the `p` direction. An arbitrary initial rotation translates this grid.

**Two distinct primes.** The only connected molecule containing both `p` and `q` has `q` p-atoms and `p` q-atoms, and bond graph `K_(q,p)`. To prove this, one p-atom meets p different q-atoms (different-prime atoms meet in at most one point). For any such q-atom, all q of its points are met by p-atoms, forcing the entire product grid and the complete bipartite graph. Same-element duplicate atoms cannot join this component.

**Colouring and planarity.** An in/out assignment exists iff the bond graph is bipartite. This does not imply a crossing-free planar graph or a physical circle-contact realisation. For example the 23-atom maximum for 2,3,5 has graph `K_(5,3)` with every edge subdivided; it is bipartite but non-planar. Whether *every* prime-element molecule is bipartite is open here; small examples cannot settle it.

## Maximum for three primes: theorem

For primes `s < p < q`, the maximum size of a connected molecule containing all three is

`M(s,p,q) = pq + (s−1)q + p`.

**Upper bound.** Regard the grid as `q` slices of size `s × p`; let `T` be the number of q-atoms. In each slice there are at most `p` possible s-lines and `s` possible p-lines. If all are present they supply two incidences per point. To accommodate the `T` q-line incidences, at least `ceil(T/p)` of these small lines must be missing in each slice (each removed line frees at most `p` incidences). This also holds when some points are unused. Thus

`N ≤ q(s+p−ceil(T/p)) + T`.

Because `1 ≤ T ≤ sp` and `q > p`, writing `k=ceil(T/p)` gives `T ≤ kp`, hence `N ≤ q(s+p) − k(q−p) ≤ q(s+p−1)+p`.

**Construction.** Put an s-line at every `(p,q)` coordinate; fill `s−1` s-coordinate layers with p-lines and the last with q-lines. Each position belongs to exactly two atoms. The graph is connected: the p-lines connect p-coordinates and the q-lines connect q-coordinates, through s-lines. Formula: `s_(pq) p_((s−1)q) q_p`. Example: `3_77 7_22 11_7` has 106 atoms. When `s=2` this becomes `2_(pq) p_q q_p`, the graph `K_(q,p)` with every edge subdivided.

## Constructions for four primes

For `s < p < q < r`, there is a connected construction with formula

`s_(pqr) p_((s−1)qr) q_((p−1)r) r_q`

and size `pqr + (s−1)qr + (p−1)r + q`. Place all s-lines; fill `s−1` s-layers with p-lines, then in the last layer fill `p−1` p-coordinate slices with q-lines and the last slice with r-lines. Every grid point has exactly two incidences and the graph is connected.

**Conjecture:** this construction is maximum for all four distinct primes. It is an achievable lower bound, not a general proof.

For 3,5,7,11 it gives `3_385 5_154 7_44 11_7`, size 590. The earlier integer optimisation in `verification/verify_max_35711.py` bounds even a relaxation of the valid connected problem by 590. It uses floating-point MILP, so this is computational evidence subject to solver tolerances, not a solver-independent proof certificate. The script also independently checks the construction.

### The 590 upper-bound relaxation

Group the 1155 grid sites by their `(7,11)` coordinates into 77 grids of size `3 × 5`. In group `(y,z)`, let `a` be the number of absent 3-lines among five possible ones, `b` the number of absent 5-lines among three, `Q_z` the number of 7-lines at that 11-coordinate, `R_y` the number of 11-lines at that 7-coordinate, and `e` the number of empty sites. Counting incidences gives `3a + 5b = Q_z + R_y + 2e`. Connectivity implies that a group with `Q_z + R_y = 0` must be empty, since no larger line can join it to another group. The MILP maximises the number of lines subject to these necessary constraints and the existence of both 7- and 11-atoms. It does not require the local counts to arise from a consistent physical arrangement, so it is an upper-bound relaxation. The supplied script obtains bound 590 and checks a construction attaining it.

For comparison, the symmetric three-layer product `3_385 5_77 7_55 11_35` has 552 atoms. A mixed example `3_385 5_143 7_55 11_5` has 588. Thus the symmetric product is not always maximal.

## Enumeration and speculative questions

An earlier search reported **35** connected 2,3,5 molecules containing all three elements, up to rotation, also 35 up to reflection; all 35 were bipartite. The original enumeration script is not available in this package, so treat this as a reported computational result rather than independently reproduced here. The report that the 23-atom maximum is unique up to rotation has the same limitation.

Earlier MILP runs reported matching lower and upper bounds for `(2,3,5,7):159`, `(2,3,5,11):247`, `(2,3,7,11):337`, `(2,5,7,13):605`, `(3,5,7,11):590`, `(3,5,7,13):696`, `(3,5,11,13):1064`, `(3,7,11,13):1376`, and `(5,7,11,13):1662`. Only the 3,5,7,11 verification is included here; the others remain unreproduced reports. Runs for `(3,5,7,17)` and `(3,7,13,17)` did not close the gap.

A broader speculation is that for every finite set of distinct primes there exists a maximum connected molecule occupying every grid point twice, with all smallest-element atoms on one side of a bipartition and a partition by other elements on the other. This is stronger and less tested than the four-prime conjecture. Questions include whether every molecule is bipartite, how to classify maxima and symmetries, what changes for composite elements, and which graphs admit physical geometric realisations.
