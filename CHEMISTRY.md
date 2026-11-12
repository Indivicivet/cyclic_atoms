# Chemistry of cyclic atoms

We can define a chemistry in which atoms remain intact, bonds may break, and
exposed points can pair with points on other fragments. The first obstruction
is conservation of each element. The second is geometric: bonds come from
exact coincidences of cyclic point sets, so an arbitrary graph rewiring need
not be possible.

Here are the main answers for distinct prime elements 3, 5 and 7. Write
`M35 = 3_5 5_3`, `M37 = 3_7 7_3`, `M57 = 5_7 7_5`, and `Dp = p_2`.
Let `Tmax = 3_35 5_14 7_5` be the 54-atom maximum molecule.

| Question | Answer under the reaction rules below |
|---|---|
| Split one Tmax entirely into M35 and M37? | No. Three copies are necessary and sufficient: `3 Tmax ⇌ 14 M35 + 5 M37`. |
| Split Tmax entirely into M35 and M57? | Impossible for any positive number of copies. With a reagent, `Tmax + 7 D5 ⇌ 7 M35 + M57`. |
| Make an arbitrary 3–5–7 molecule using binaries, with no other products? | Some batch always works; its minimum size divides 105. A single copy never works. |
| Make one arbitrary 3–5–7 molecule if dimer byproducts are allowed? | Yes. Even M35 and M37 alone supply enough atoms, with suitable excess reactants. |
| Join two binaries without atomizing everything? | Yes: `M35 + M37 ⇌ (3_10 5_3 7_3) + D3`, by cutting six bonds. |

The finite assertion that a single copy never works is checked exhaustively
using the complete parity parameterization proved below. It is not based on a
random sample. These results concern mathematical reachability under the
specified rules; we have not defined energies, reaction rates, or continuous
motion.

## A reaction with six broken bonds

![Cutting two atoms out and joining their neighbours](chemistry/output/fusion.png)

Take M35 and M37 in separate frames. In each, select a 3-atom and rotate the
frames so that the selected atoms would have the same point set.

1. Cut all three bonds of each selected atom and extract the two intact atoms.
2. Superpose the two remaining fragments. Their three exposed sites coincide
   in pairs and become three 5–7 bonds.
3. Pair the two extracted 3-atoms with one another in a separate frame, making
   D3 with three parallel bonds.

No atom changes element or disappears. Both fragments before joining are open
configurations, rather than molecules. Their graphs are `K(4,3)` and `K(6,3)`;
the product joins these graphs by a matching of three edges. Its formula is
`3_10 5_3 7_3`, with 16 atoms and 33 bonds. Together with D3, it has the same 18
atoms and 36 bonds as the reactants.

Why does the geometry work? After aligning the selected s-atoms, the point
grids of M(s,p) and M(s,q) intersect in exactly their s points. Removing those
atoms leaves occupancy one at the intersection and occupancy two elsewhere.
Superposing the fragments therefore gives exact double occupancy, without
any triple intersections. Each fragment is connected, and the s new edges
join them.

This proves the general joining rule for three distinct primes:

$$
M(s,p)+M(s,q)\;\rightleftharpoons\;
T\bigl(s_{p+q-2}\,p_s\,q_s\bigr)+D_s.
$$

The mechanism cuts `2s` old bonds and makes `2s` new bonds, including the dimer
bonds. It is a construction, with no claim that it minimizes the number of
cuts.

| Shared element | Binary reactants | Ternary product | Byproduct |
|---|---|---|---|
| 3 | M35 + M37 | `3_10 5_3 7_3` (16 atoms) | D3 |
| 5 | M35 + M57 | `3_5 5_8 7_5` (18 atoms) | D5 |
| 7 | M37 + M57 | `3_7 5_7 7_6` (20 atoms) | D7 |

## Configurations during a reaction

The definitions of atoms and molecules in [INTRO.md](INTRO.md) still apply.
The extra definitions and rules used here are:

- An **open configuration** has occupancy one or two at every occupied site.
  A site of occupancy one is an **open site**. Occupancy above two is forbidden.
- A **closed configuration** has occupancy two at every occupied site. Its
  connected components are molecules. Several molecules can coexist.
- A **fragment** is a group of intact atoms that we keep together while
  rotating it. It may be open or closed. Separate fragments initially have
  independent angular frames.
- To **cut**, partition a configuration into fragments and separate their
  frames. Each bond crossing the partition becomes two open sites. The atoms
  inside each fragment keep their relative phases.
- To **join**, choose one rigid rotation per fragment and superpose them.
  Coincident open sites pair automatically. Every coincidence must have total
  occupancy at most two; overlapping an open site with an existing bond is
  forbidden.
- A **reaction** conserves the number of atoms of every element. Atoms may be
  isolated as intermediate fragments. A reaction arrow here means existence
  of a finite sequence of these discrete operations, reversible step by step.

Separating frames is part of this proposed chemistry. If all phases stay fixed
in one frame, deleting an edge alone cannot break a bond: its two points still
coincide. Nor can a proper, nonempty subset of a connected molecule already be
closed in the inherited frame; connectivity supplies a crossing bond.

For two fragments with occupancy functions `mF` and `mG`, a rotation `theta`
is an admissible join precisely when

$$
m_F(t)+m_G(t-\theta)\le 2\qquad\text{for every }t.
$$

Every new bond is an intersection of their open-site sets. Connectivity and
absence of remaining open sites then decide whether the result is a molecule.
Matching vertex degrees alone does not establish a geometric join.

If a configuration has B bonds and U open sites, the bookkeeping identity is

$$
\sum_p p n_p=2B+U.
$$

Cutting k bonds raises U by `2k`; forming k bonds lowers it by `2k`. A closed
reaction conserves the total bond count between its endpoints, because each
atom has a fixed number of points. An energy assigned solely to the number of
bonds would therefore give equal endpoint energies to all closed products
with the same inventory. Bond-type energies and activation costs would be
additional choices, rather than consequences of the present definitions.

## The maximum molecule and its symmetry

![The 54-atom maximum as a row and column bond graph](chemistry/output/maximum_graph.png)

Every purple vertex is a 3-atom. The two orange vertices beside each row are
distinct 5-atoms with the same five neighbours. Each teal vertex joins all
seven purple vertices in its column. All 54 atoms and all 105 bonds are drawn;
crossings of curves do not introduce vertices.

This makes the abstract graph symmetries visible: any permutation of the five
columns, any permutation of the seven rows, and an independent swap of the
two 5-atoms in each row preserves the graph. These generate the full
element-preserving graph automorphism group
`(C2)^7 ⋊ (S5 × S7)`. This is much larger than the geometric rotational
symmetry, which has order 35 for this construction. Graph isomorphism and
equivalence of cyclic configurations are different questions.

## Stoichiometry of binary reagents

For a target formula `3_n3 5_n5 7_n7`, suppose X copies of M35, Y of M37 and Z
of M57 supply exactly its atoms. Conservation requires

$$
n_3=5X+7Y,\qquad n_5=3X+7Z,\qquad n_7=3Y+5Z.
$$

There is a unique rational solution:

$$
X=\frac{3n_3+5n_5-7n_7}{30},\qquad
Y=\frac{3n_3-5n_5+7n_7}{42},\qquad
Z=\frac{-3n_3+5n_5+7n_7}{70}.
$$

For one target copy, all three must be nonnegative integers. For a batch of K
copies, `KX`, `KY`, `KZ` must be nonnegative integers. If a coefficient is
negative, multiplying the batch cannot fix it. If all are nonnegative, the
minimum batch is the least common multiple of their reduced denominators.

For Tmax these coefficients are `(14/3, 5/3, 0)`. Thus a single copy cannot
split entirely into binary molecules, whereas

$$
3T_{\max}\;\rightleftharpoons\;14M35+5M37.
$$

![All atoms in the three-copy splitting reaction](chemistry/output/batch_split.png)

The intermediate drawn is complete dissociation. It contains 105 3-atoms, 42
5-atoms and 15 7-atoms, with 630 open sites. This supplies an existence proof;
finding a mechanism that keeps larger fragments intact is a separate problem.

Using only M35 and M57 would require

$$
5n_5=3n_3+7n_7.
$$

Tmax fails this equality: its two sides are 70 and 140. It needs fourteen
additional 5-atoms, giving the balanced reaction

$$
T_{\max}+7D5\;\rightleftharpoons\;7M35+M57.
$$

The dimers are consumed in this direction; they are reagents, not catalysts.

## Why every three-prime molecule has a binary batch recipe

The following gives a complete parameterization of the possible line
occupancies, and a proof of the batch claim. It also proves that every
three-prime molecule is bipartite. These arguments have exact Python checks,
but have not been formalized in Lean.

### Parity parameterization

Let the three distinct primes be s, p, q. Rotate a molecule onto the grid
`Z_s × Z_p × Z_q`, as in [THEORY.md](THEORY.md). A molecule using all three
elements cannot contain two identical atoms: such a pair would be an isolated
dimer. Therefore each possible coordinate line is either absent or present
once. Write its presence indicator as

$$
A(y,z),\quad B(x,z),\quad C(x,y)\in\{0,1\}.
$$

At each point, `A+B+C` is either zero or two. Equivalently, over the field with
two elements,

$$
A(y,z)\oplus B(x,z)\oplus C(x,y)=0.
$$

All solutions have the form

$$
A(y,z)=\beta_y\oplus\gamma_z,\qquad
B(x,z)=\alpha_x\oplus\gamma_z,\qquad
C(x,y)=\alpha_x\oplus\beta_y.
$$

For completeness, fix the coordinate values `x=y=z=0`, and choose
`beta_y=C(0,y)`, `gamma_z=B(0,z)` and
`alpha_x=B(x,0) xor B(0,0)`. The parity equations at `(x,y,0)` and `(0,y,0)`
give `C(x,y)=alpha_x xor beta_y`; substituting back gives the other two
identities. Thus this parameterization misses no solutions. Conversely,
these identities give even occupancy, and with only three available lines
that means occupancy zero or two. Some choices give disconnected closed
configurations, so connectivity must still be checked.

Simultaneously complementing all bits leaves every line unchanged. For fixed
coordinates this is the only redundancy. Coordinate permutations preserve
incidence and the abstract graph, but generally are not circle rotations.

### Bipartiteness

Color each present s-line by `beta_y`, each p-line by `gamma_z`, and each
q-line by `alpha_x`. If a point is occupied, its three coordinate bits are not
all equal. If `alpha_x` is the odd one out, the bond is between the p- and
q-lines and their colors differ. The other two cases work cyclically. Hence
every bond has opposite colors at its ends.

Together with the elementary two-prime and dimer cases, this proves
bipartiteness for every prime-element molecule with at most three elements.
The four-or-more-element question is not settled by this argument.

### Nonnegative binary coefficients

Let a, b, c be the numbers of 1 bits among the s, p, q coordinates. Counting
lines gives

$$
n_s=b(q-c)+(p-b)c,\qquad
n_p=a(q-c)+(s-a)c,\qquad
n_q=a(p-b)+(s-a)b.
$$

The unique rational binary recipe has coefficients

$$
X_{sp}=\frac{s n_s+p n_p-q n_q}{2sp}
=\frac{c(s-a)(p-b)+(q-c)ab}{sp},
$$

$$
X_{sq}=\frac{s n_s-p n_p+q n_q}{2sq}
=\frac{b(s-a)(q-c)+(p-b)ac}{sq},
$$

$$
X_{pq}=\frac{-s n_s+p n_p+q n_q}{2pq}
=\frac{a(p-b)(q-c)+(s-a)bc}{pq}.
$$

Every term in the final numerators is nonnegative. Their reduced denominators
divide `sp`, `sq`, `pq`, respectively, so their least common multiple divides
`spq`. Multiplying by that least common multiple gives a balanced binary
recipe. This proves that **every three-prime molecule has a recipe for some
batch of at most spq copies**.

Which two kinds of binary suffice is also explicit. For example, M(s,p) and
M(s,q) suffice exactly when `X_pq=0`, meaning both terms in its nonnegative
numerator vanish. A molecule with all three coefficients positive requires
all three kinds if no other products or reagents are allowed.

### Complete check for 3–5–7

Complement the bits if necessary so that `a` is 0 or 1. Then the 96 triples
`a in {0,1}`, `b in {0,...,5}`, `c in {0,...,7}` cover every possible formula
and graph, with possible repetitions of isomorphic graphs. Permuting
coordinates within each bit class proves that the weights alone determine
the graph up to isomorphism. They do not classify geometric molecules up to
rotation or reflection.

Of these 96 profiles, 80 give connected configurations with all three
elements. None has an integral one-copy binary recipe. The exact enumeration
is in [weight_profiles.csv](chemistry/output/weight_profiles.csv), reproduced
by `python -m chemistry.examples`. This completes the finite check underlying
the single-copy assertion at the start.

For example, `(a,b,c)=(1,1,1)` gives `3_10 5_8 7_6`. All three coefficients
are positive: `(14/15,16/21,26/35)`. Its minimum batch is 105:

$$
105T_{24}\;\rightleftharpoons\;98M35+80M37+78M57.
$$

![A molecule requiring all three binary kinds in a pure batch recipe](chemistry/output/mixed_graph.png)

## What makes a balanced recipe sufficient?

Under our permissive discrete rules, any two specified collections of
molecules with the same element inventory are mutually reachable. Fully
separate their atoms, then assemble the desired products one atom at a time.
The issue is keeping different frames from accidentally overlapping.

For rational phases, choose a grid size G divisible by all phase denominators
and all atom elements in both collections. Assign distinct offsets
`j/(DG)`, with distinct `0 < j < D`, to every reactant frame, product frame
and temporary single-atom frame. Their supports lie in distinct cosets of
the `1/G` grid, so they do not intersect. Move each reactant atom to its
temporary frame, then move it to its intended product position. Removing
atoms cannot raise occupancy. Adding a subset of a valid product cannot
exceed that product's double occupancy. Temporary frames remain disjoint.

This is implemented in `chemistry.model.atomization_path`. It assigns stable
atom identities and exact rational phases. The saved
[batch_path.json](chemistry/output/batch_path.json) contains initial, isolated
and final states and 324 individual atom moves for the maximum example.
Verification checks every intermediate state, including occupancy and
element conservation.

These are discrete changes of phase. We have not proved that one can
interpolate each move by a continuous rotation on a single circle while
forbidding triple occupancy throughout the motion. That would require a
further choice of dynamics and separation rules. The construction also
permits transient bonds to break freely; it does not imply an efficient
reaction mechanism.

## A single product with dimer byproducts

If surplus atoms may leave as dimers, one copy of any 3–5–7 molecule can be
made from M35 and M37 alone. Choose nonnegative integers X and Y large enough
that `3X >= n5`, `3Y >= n7`, and `5X+7Y >= n3`, with `X ≡ n5 (mod 2)` and
`Y ≡ n7 (mod 2)`. Increase X or Y by two as needed. The surplus 5- and 7-atoms
are even in number. The surplus 3-atoms are also even because
`n3+n5+n7` is even for a closed molecule of odd-degree atoms. Pair each
surplus element into dimers:

$$
X M35+Y M37\;\rightleftharpoons\;
T+\frac{5X+7Y-n_3}{2}D3
+\frac{3X-n_5}{2}D5+\frac{3Y-n_7}{2}D7.
$$

For Tmax, one choice is `6 M35 + 3 M37 ⇌ Tmax + 8 D3 + 2 D5 + 2 D7`.
The earlier six-cut fusion is a much smaller example of the same distinction:
one target plus a byproduct is possible even when a pure one-copy binary
recipe is not.

## Reproduce and explore

From the repository root, using the existing requirements:

```sh
python -m chemistry.examples
python -m chemistry.verify
```

`examples` writes four figures in PNG and SVG, exact 0A-compatible JSON for
three molecules, the reaction path, and the complete weight table to
`chemistry/output/`. Use `--outdir DIR` to choose another destination.
The existing renderers can read the JSON, for example:

```sh
python visualization/graph.py chemistry/output/fusion_357.json
python visualization/circle.py chemistry/output/maximum_357.json
```

The Python entry points are `inspect_open`, `fragment`, `rotate`, `join`,
`binary_molecule`, `binary_fusion`, `parity_configuration`,
`binary_requirements`, `batch_recipe`, and `atomization_path` in
[chemistry/model.py](chemistry/model.py). Phases use `fractions.Fraction`.
Reaction paths use unsigned atoms; an in/out assignment is a property of a
particular bond graph, rather than an extra conserved element.

The next useful problems are the minimum number of cuts for a given reaction,
reachability while retaining specified fragments, and which joins are allowed
by a chosen continuous dynamics. An energy model would also let us distinguish
possible reactions from preferred reactions.
