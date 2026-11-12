# Chemistry of cyclic atoms

For reactions whose states contain only molecules, see [CLOSED_CHEMISTRY.md](CLOSED_CHEMISTRY.md). The 3→19 split cannot be composed from closed steps with at most two inputs and two outputs, starting with only maxima and no additional reagents.

We can define reactions where atoms stay intact, bonds break, and exposed points pair with points on other fragments. Two constraints govern which reactions exist. Element counts must match, and new bonds must come from exact coincidences of cyclic point sets.

For distinct prime elements 3, 5, and 7, write `M35 = 3_5 5_3`, `M37 = 3_7 7_3`, `M57 = 5_7 7_5`, and `Dp = p_2`. Let `Tmax = 3_35 5_14 7_5` be the 54-atom maximum molecule.

| Question | Answer |
|---|---|
| Split one Tmax into M35 and M37? | No. Three copies are needed: `3 Tmax ⇌ 14 M35 + 5 M37`. |
| Split Tmax into M35 and M57? | Impossible for any batch size alone. With a dimer reagent, `Tmax + 7 D5 ⇌ 7 M35 + M57`. |
| Make an arbitrary 3-5-7 molecule from binaries alone? | Some batch dividing 105 always works. A single copy never does. |
| Make one arbitrary 3-5-7 molecule if dimer byproducts are allowed? | Yes, even from M35 and M37 alone. |
| Join two binaries without full atomization? | Yes: `M35 + M37 ⇌ (3_10 5_3 7_3) + D3`, cutting six bonds. |

## A six-cut reaction

![Cutting two atoms out and joining their neighbours](chemistry/output/fusion.png)

Take M35 and M37 in separate frames. In each, pick a 3-atom and rotate the frames so the two chosen atoms sit at the same angles.

1. Cut all three bonds of each chosen 3-atom and pull both atoms out.
2. Superpose the two remaining fragments. Their three open sites line up in pairs, forming three 5-7 bonds.
3. Pair the two extracted 3-atoms in their own frame to make D3.

Before joining, the two stripped fragments have graphs `K(4,3)` and `K(6,3)`. Superposing them adds a three-edge matching between the 5-atoms and 7-atoms, giving a 16-atom molecule `3_10 5_3 7_3` with 33 bonds. Together with D3, the products keep all 18 atoms and 36 bonds.

The geometry works because the point grids of `M(s,p)` and `M(s,q)` meet purely at the `s` points of the aligned `s`-atoms. Removing those two atoms drops occupancy at those `s` points from two to one in each fragment, while every other occupied point stays at two on disjoint cosets. Superposing the fragments puts occupancy two everywhere with no triple collisions.

In general, for distinct primes `s, p, q`, cutting `2s` bonds joins `M(s,p)` and `M(s,q)`:

$$
M(s,p)+M(s,q)\;\rightleftharpoons\;
T\bigl(s_{p+q-2}\,p_s\,q_s\bigr)+D_s.
$$

| Shared element | Binary reactants | Ternary product | Byproduct |
|---|---|---|---|
| 3 | M35 + M37 | `3_10 5_3 7_3` (16 atoms) | D3 |
| 5 | M35 + M57 | `3_5 5_8 7_5` (18 atoms) | D5 |
| 7 | M37 + M57 | `3_7 5_7 7_6` (20 atoms) | D7 |

## Reaction rules

Building on the definitions in [INTRO.md](INTRO.md):

- An *open configuration* has occupancy one or two at every occupied site. A site of occupancy one is an *open site*. Occupancy above two is forbidden.
- A *closed configuration* has occupancy two at every occupied site. Its connected components are molecules.
- A *fragment* is a group of intact atoms rotated together. Separate fragments sit in independent angular frames.
- To *cut*, partition a configuration into fragments in separate frames. Every bond crossing the partition turns into two open sites, while atoms inside the same fragment keep their relative phases.
- To *join*, rotate each fragment rigidly and superpose them into one frame. Coincident open sites pair into bonds, provided total occupancy never exceeds two:

$$
m_F(t)+m_G(t-\theta)\le 2\qquad\text{for all }t.
$$

A configuration with `B` bonds and `U` open sites satisfies

$$
\sum_p p n_p=2B+U.
$$

Cutting `k` bonds increases `U` by `2k`, and forming `k` bonds decreases it by `2k`. Any reaction between closed configurations preserves the total bond count $\frac{1}{2}\sum_p p n_p$.

## The maximum molecule and its symmetry

![The 54-atom maximum as a row and column bond graph](chemistry/output/maximum_graph.png)

In this layout of `Tmax = 3_35 5_14 7_5`, each purple vertex is a 3-atom at a grid coordinate `(y, z)` in `Z_5 × Z_7`. The two orange vertices beside each row are 5-atoms sharing the same five 3-atom neighbours, and each teal vertex is a 7-atom connected to the seven 3-atoms in its column.

Permuting the five columns, permuting the seven rows, or swapping the two 5-atoms within any row preserves the graph, generating the element-preserving automorphism group `(C2)^7 ⋊ (S5 × S7)`. The geometric rotational symmetry group on the circle has order 35.

## Stoichiometry of binary reagents

To build a target formula `3_n3 5_n5 7_n7` purely from `X` copies of M35, `Y` of M37, and `Z` of M57, element conservation requires

$$
n_3=5X+7Y,\qquad n_5=3X+7Z,\qquad n_7=3Y+5Z.
$$

Solving for `X, Y, Z` gives

$$
X=\frac{3n_3+5n_5-7n_7}{30},\qquad
Y=\frac{3n_3-5n_5+7n_7}{42},\qquad
Z=\frac{-3n_3+5n_5+7n_7}{70}.
$$

A batch of `K` copies has a pure binary recipe when `KX, KY, KZ` are nonnegative integers. When `X, Y, Z >= 0`, the smallest valid batch `K` is the least common multiple of their reduced denominators.

For `Tmax`, `(X, Y, Z) = (14/3, 5/3, 0)`, so a single copy cannot split into binary molecules, while three copies split as

$$
3T_{\max}\;\rightleftharpoons\;14M35+5M37.
$$

![All atoms in the three-copy splitting reaction](chemistry/output/batch_split.png)

Using only M35 and M57 (`Y = 0`) requires `5n_5 = 3n_3 + 7n_7`, which fails for `Tmax` (`70 != 140`). Supplying seven 5-atom dimers balances the deficit:

$$
T_{\max}+7D5\;\rightleftharpoons\;7M35+M57.
$$

## Splitting three maxima in 140 cuts

The reaction `3 Tmax → 14 M35 + 5 M37` can be carried out by breaking 140 of the 315 bonds and keeping the other 175 intact.

![Reagents and outputs in the curved in/out style](chemistry/output/minimum_split_human.png)

### Cut two copies one way, and the third the other way

Label the three copies of `Tmax` as A, B, and C.

1. Strip all fourteen 5-atoms from C (`14 × 5 = 70` cuts). What remains of C splits into five `F37 = 3_7 7_1` stars, each holding one 7-atom, seven 3-atoms, seven intact bonds, and fourteen open sites.
2. Strip all five 7-atoms from A and from B (`2 × 5 × 7 = 70` cuts). A and B each split into seven `F35 = 3_5 5_2` fragments with graph `K(5,2)`, ten intact bonds, and five open sites.
3. Drop one free 5-atom from C into each of the fourteen `F35` fragments to form fourteen M35 molecules.
4. Drop two free 7-atoms from A and B into each of the five `F37` stars to form five M37 molecules.

![Which bonds are cut and which fragments survive](chemistry/output/minimum_split_cuts.png)

At the intermediate stage between cutting and rejoining, the fragments and free atoms are

$$
14F35+5F37+14A_5+10A_7,
\qquad F35=3_5\,5_2,\quad F37=3_7\,7_1,
$$

with `14 × 10 + 5 × 7 = 175` surviving bonds.

![The two fragment completion steps](chemistry/output/minimum_split_completion.png)

### Circle geometry of the joins

In CRT coordinates `(x, y, z)` on `Z_3 × Z_5 × Z_7`, `Tmax` places 7-lines at `x = 0` and 5-lines at `x = 1, 2`.

Each `F35` fragment is a fixed-`z` slice with its `x = 0` 7-atoms removed, leaving five open sites along the missing `(x = 0, z)` 5-line. Rotating a free 5-atom into that line closes the fragment into M35.

Similarly, each `F37` star is a fixed-`y` slice missing its two 5-lines at `x = 1, 2`, leaving fourteen open sites along those two 7-lines. Rotating two free 7-atoms into `x = 1` and `x = 2` closes the star into M37.

![The open fragments in the curved style](chemistry/output/minimum_split_fragments_human.png)

### Why 140 cuts is the minimum

Every 3-atom in `Tmax` starts with two bonds to 5-atoms and one bond to a 7-atom. In the products, the 70 3-atoms ending up in `14 M35` have no 7-atom neighbours, so each must lose its 3-7 bond (70 cuts). The 35 3-atoms ending up in `5 M37` have no 5-atom neighbours, so each must lose both of its 3-5 bonds (`35 × 2 = 70` cuts). Because every bond in `Tmax` has a single 3-atom endpoint, these `70 + 70 = 140` bonds are distinct, so at least 140 cuts are required.

### Stages and reproduction

| Stage | Bonds present | Open sites | Connected components |
|---|---:|---:|---:|
| Three starting molecules | 315 | 0 | 3 |
| Strip C's 5-atoms | 245 | 140 | 21 |
| Strip A and B's 7-atoms | 175 | 280 | 43 |
| Complete fourteen M35 | 245 | 140 | 29 |
| Complete five M37 | 315 | 0 | 19 |

![Every atom at five stages](chemistry/output/minimum_split_stages.png)

Run:

```sh
python -m chemistry.minimum_split
python -m chemistry.verify
```

`minimum_split` writes the five figures above and the 67-step reaction trajectory to [minimum_split_path.json](chemistry/output/minimum_split_path.json) (see [minimum_split.py](chemistry/minimum_split.py) and [split_plots.py](chemistry/split_plots.py)).

## Why every three-prime molecule has a binary batch recipe

### Parity parameterization

Rotate a molecule with distinct primes `s, p, q` onto the grid `Z_s × Z_p × Z_q`. A molecule using all three elements cannot contain two identical atoms (which would form an isolated dimer), so each coordinate line appears at most once. Write the line indicators as

$$
A(y,z),\quad B(x,z),\quad C(x,y)\in\{0,1\}.
$$

Every grid point has occupancy zero or two, which over `GF(2)` is

$$
A(y,z)\oplus B(x,z)\oplus C(x,y)=0.
$$

Setting `beta_y = C(0,y)`, `gamma_z = B(0,z)`, and `alpha_x = B(x,0) xor B(0,0)` shows that the general solution is

$$
A(y,z)=\beta_y\oplus\gamma_z,\qquad
B(x,z)=\alpha_x\oplus\gamma_z,\qquad
C(x,y)=\alpha_x\oplus\beta_y.
$$

Flipping all bits simultaneously leaves `A, B, C` unchanged and is the only redundancy at fixed coordinates.

### Bipartiteness

Color each present `s`-line by `beta_y`, each `p`-line by `gamma_z`, and each `q`-line by `alpha_x`. At any occupied point `(x, y, z)`, two of the three bits `(alpha_x, beta_y, gamma_z)` agree and the third differs, so the two lines meeting at `(x, y, z)` always carry opposite colors. Together with the two-prime and dimer cases, every molecule with at most three prime elements is bipartite.

### Nonnegative binary coefficients

Let `a, b, c` be the numbers of 1s in `alpha, beta, gamma`. The atom counts are

$$
n_s=b(q-c)+(p-b)c,\qquad
n_p=a(q-c)+(s-a)c,\qquad
n_q=a(p-b)+(s-a)b.
$$

Substituting these into the binary stoichiometry formulas gives

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

Because `0 <= a <= s`, `0 <= b <= p`, and `0 <= c <= q`, all three numerators are nonnegative, and the reduced denominators divide `sp`, `sq`, and `pq`. Their least common multiple divides `spq`, so every three-prime molecule has a pure binary recipe in a batch of size dividing `spq`.

### Complete check for 3-5-7

After flipping all bits if needed so `0 <= a <= 1`, the `2 × 6 × 8 = 96` weight triples `(a, b, c)` determine the bond graph up to isomorphism. Of these 96 triples, 80 produce connected molecules containing all three elements, and none has integer `(X, Y, Z)` for a single copy (see [weight_profiles.csv](chemistry/output/weight_profiles.csv)).

For example, `(a, b, c) = (1, 1, 1)` gives the 24-atom molecule `3_10 5_8 7_6` with `(X, Y, Z) = (14/15, 16/21, 26/35)` and minimum batch size 105:

$$
105T_{24}\;\rightleftharpoons\;98M35+80M37+78M57.
$$

![A molecule requiring all three binary kinds in a pure batch recipe](chemistry/output/mixed_graph.png)

## Disjoint frames for full dissociation

Any balanced reaction can be stepped through atom by atom if we park isolated atoms in non-overlapping frames. Choose a grid denominator `G` divisible by all phase denominators and atom elements in the reactants and products, and assign each reactant, product, and temporary single-atom frame its own offset `j / (DG)` for distinct `0 < j < D`. Because these offsets sit in disjoint cosets of `(1/G)Z/Z`, atoms in different frames never collide as they are pulled out of the reactants and placed into the products. `chemistry.model.atomization_path` builds this trajectory and writes the 324-step `3 Tmax` dissociation path to [batch_path.json](chemistry/output/batch_path.json).

## Single-copy reactions with dimer byproducts

If surplus atoms can pair off as dimers, a single copy of any 3-5-7 molecule `T` can be made from M35 and M37 alone. Pick nonnegative integers `X, Y` with `3X >= n_5`, `3Y >= n_7`, `5X + 7Y >= n_3`, `X ≡ n_5 (mod 2)`, and `Y ≡ n_7 (mod 2)`. Because `n_3 + n_5 + n_7` is even in any closed configuration of odd-degree atoms, `5X + 7Y - n_3` is also even, and the leftover atoms pair into dimers:

$$
X M35+Y M37\;\rightleftharpoons\;
T+\frac{5X+7Y-n_3}{2}D3
+\frac{3X-n_5}{2}D5+\frac{3Y-n_7}{2}D7.
$$

For `Tmax`, `X = 6, Y = 3` gives `6 M35 + 3 M37 ⇌ Tmax + 8 D3 + 2 D5 + 2 D7`.

## Scripts

```sh
python -m chemistry.examples
python -m chemistry.verify
```

`examples` writes the figures, 0A-compatible molecule JSONs (`fusion_357.json`, `maximum_357.json`, `mixed_357.json`), `batch_path.json`, and `weight_profiles.csv` to `chemistry/output/`. These JSON files work directly with the existing visualizers:

```sh
python visualization/graph.py chemistry/output/fusion_357.json
python visualization/circle.py chemistry/output/maximum_357.json
```
