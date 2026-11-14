# Universal synthesis from any two binary feeds

Using the closed-endpoint reaction model from [CLOSED_CHEMISTRY.md](CLOSED_CHEMISTRY.md) with molecular byproducts allowed, any molecule whose elements lie in `{3, 5, 7}` can be formed from an initial pool containing only any two of `M35 = (5,3,0)`, `M37 = (7,0,3)`, and `M57 = (0,7,5)` (counts of elements 3, 5, and 7). The construction uses only `2→2` element-conserving molecular steps.

## Theorem: universal synthesis for any three distinct primes

Let `p`, `q`, and `r` be three distinct primes, and write formulas in that order:

$$
M_{pq}=(q,p,0),\qquad M_{pr}=(r,0,p),\qquad M_{qr}=(0,r,q),
$$

with dimers `Dp = (2,0,0)`, `Dq = (0,2,0)`, and `Dr = (0,0,2)`.
Every molecule whose elements lie in `{p,q,r}` can be constructed from a
finite initial stock using only any chosen two of these three binary species.
Every reaction has exactly two molecular inputs and two molecular outputs
and conserves each element. The final stock contains the requested molecule;
other molecular products are allowed. No intermediate molecules need to be
supplied initially or borrowed. This includes triples containing the prime 2.

### Proof

Use the [parity parameterization](CHEMISTRY.md#parity-parameterization), with
weights `0 ≤ a ≤ p`, `0 ≤ b ≤ q`, and `0 ≤ c ≤ r`, and denote its formula by

$$
F(a,b,c)=\bigl(b(r-c)+(q-b)c,\ a(r-c)+(p-a)c,\ a(q-b)+(p-a)b\bigr).
$$

The complete molecular formula catalog consists of the three dimers, the
three binaries, and the profiles `F(a,b,c)` whose three counts are positive.
Here is why the same classification works for arbitrary distinct primes.
Connectedness aligns the atoms to a translate of the `pqr` circle grid; the
Chinese remainder theorem identifies this with `Zp × Zq × Zr`. Coincident
lines force an isolated dimer. Otherwise, each line is used at most once,
and exact pairing gives the Boolean equation
`A(y,z) xor B(x,z) xor C(x,y) = 0`. Its general solution is the three-list
parity parameterization. If an element is missing, connectedness confines
the molecule to one slice, giving the corresponding binary.

Conversely, every positive three-element profile is connected. To check
this, split the present lines into the six classes `A01`, `B01`, `C01`,
`A10`, `B10`, `C10`, according to their fixed coordinate bits. Bonds follow
the cycle
`A01–B01–C01–A10–B10–C10–A01`.
When all three weights are interior, the path `B01–C01–A10` already connects
all its individual lines: passing through `C01` changes the `z` index,
through `A10` changes `x`, and through `B01` changes `y`. Each of the other
three classes attaches to this connected part along the cycle. A boundary
weight deletes two classes, leaving a connected four-class path by the
same argument, after permuting coordinates or complementing all bits.
With two boundary weights, positivity requires their bits to be opposite;
the remaining three classes form precisely such a connected three-class
path. All three boundary weights cannot give three positive counts. Every occupied grid point has
two lines, so these connected configurations are molecules.

Relabel the primes so that `p,q ≥ 3` and `r ≥ 2`. First suppose the feeds
are `Mpq` and `Mpr`. The following identities give legal reactions:

1. **Obtain the boundary strips.** Fusion gives
   `Mpq + Mpr → F(0,1,1) + Dp`. Since `F` is affine in each weight,

   $$
   2F(a,b,c)=F(a-1,b,c)+F(a+1,b,c),
   $$

   and likewise for `b` and `c`. From a seed at weight 1, these reactions
   reach every weight in a legal integer interval. In particular, they give
   `F(0,1,c)` for `0 ≤ c ≤ r` and `F(0,b,1)` for `0 ≤ b ≤ q`.
   Their weight-zero endpoints are `Mpr` and `Mpq`; every other endpoint
   has three positive counts.

2. **Enter the interior.** Apply

   $$
   F(0,1,r-1)+F(0,q-1,1)
   \longrightarrow F(1,1,r-1)+F(1,q-1,1).
   $$

   Both outputs are positive profiles. Midpoint reactions, starting from
   `b=q-1` and moving in the reversed `b` direction, give `F(1,1,1)`.

3. **Reach all positive profiles.** First vary `a` with `b=c=1`. For each
   interior `a`, vary `b` with `c=1`; for each interior `a,b`, vary `c`.
   This reaches every profile with `a,b` interior. Varying `b` or `a`
   next reaches all profiles with any two weights interior. The remaining
   positive profiles have one interior weight and two opposite boundary
   bits. Reach a boundary by splitting at its adjacent interior weight:
   for example, `2F(a,1,r) → F(a,0,r) + F(a,2,r)`.
   Use the `b` direction when `a` is interior and the `a` direction
   otherwise. The assumptions `p,q ≥ 3` keep the other output interior
   in that direction, so both outputs remain positive molecules.

4. **Reach the missing binary and dimers.** The reaction

   $$
   2F(1,1,0)\longrightarrow M_{qr}+F(1,2,0)
   $$

   produces `Mqr`; the second output is positive because `p ≥ 2`, `q ≥ 3`.
   Fuse binary pairs sharing each element to obtain all three dimers.

For any other feed pair, first produce its missing binary using steps 1–2,
the interior part of step 3, and the missing-binary reaction in step 4,
naming the shared element first and choosing an odd prime
as the second coordinate. That part of the construction only requires
the shared element to be at least 2, the second dimension at least 3, and
the third at least 2. Thus it also works when the shared element is 2.
Once all three binaries are producible, apply the construction with the
two odd primes in the first two coordinates.

Each use of a producible input can be prepared on fresh feed copies.
Concatenate the two preparations and then run their reaction, retaining
all unused products. Induction on the finite production tree therefore
gives an ordered finite batch. Finally, the endpoint rule allows any
geometric isomer with a produced formula to be chosen as that output,
including the original requested molecule. ∎

### Lean proof from the original molecule definition

The public theorem is `GeneralSynthesis.every_molecule_with_elements` in
[`GeneralSynthesis.lean`](lean/CyclicAtoms/GeneralSynthesis.lean). Its
hypotheses are three pairwise distinct natural primes `p,q,r`, an original
`IsMolecule C`, the restriction of its elements to `{p,q,r}`, and a choice
of binary feed pair. It concludes that finite initial and final stocks of
actual molecules are connected by a `MolecularChain` and that `C` itself
occurs in the final stock. Every reaction has exactly two inputs and two
outputs and conserves every natural-number element. Neither a catalog
membership assumption nor a geometric realization assumption is required.
The primes may be supplied in any order, including `p=2` or `q=2`.

The relationship between formulas and geometry is also an explicit theorem:
`GeneralSynthesis.valid_iff_original_molecule` proves

```lean
Valid t.p t.q t.r f ↔
  ∃ C : Config, IsMolecule C ∧ Elements t.p t.q t.r C ∧
    configFormula t.p t.q t.r C = f
```

Here `t` contains the three primes and their distinctness proofs.
`f` is the triple of atom counts `(np,nq,nr)`, not an extra geometric
parameter. The right-hand side asserts existence of an original molecule
with those counts; it does not identify all configurations with the same
formula. The synthesis theorem retains the particular requested isomer.

The proof separates into checked geometric and synthesis results:

- [`PrimeGeometry.lean`](lean/CyclicAtoms/PrimeGeometry.lean) proves general
  CRT alignment and the exact correspondence between coordinate lines and
  original cyclic atom point sets.
- [`OriginalClassification.lean`](lean/CyclicAtoms/OriginalClassification.lean)
  derives catalog membership from `IsMolecule`. Repeated identical lines
  give an isolated dimer; injective lines give a paired connected grid.
- [`PrimeGridCounting.lean`](lean/CyclicAtoms/PrimeGridCounting.lean) and
  [`PrimeGridClassification.lean`](lean/CyclicAtoms/PrimeGridClassification.lean)
  prove parity counting and classification, including missing-element binaries.
- [`PrimeGridRealization.lean`](lean/CyclicAtoms/PrimeGridRealization.lean) and
  [`PrimeMoleculeWitness.lean`](lean/CyclicAtoms/PrimeMoleculeWitness.lean)
  construct actual `IsMolecule` witnesses for every catalog formula, proving
  both exact pairing and connectedness.
- [`UniversalSynthesis.lean`](lean/CyclicAtoms/UniversalSynthesis.lean) proves
  the symbolic construction and finite batches;
  [`FormulaPermutations.lean`](lean/CyclicAtoms/FormulaPermutations.lean)
  removes the ordering restriction on the dimensions.
- [`MolecularSynthesis.lean`](lean/CyclicAtoms/MolecularSynthesis.lean)
  lifts batches to actual molecular stocks, choosing `C` itself when its
  formula is produced. The public theorem supplies the proved classification
  and realization results to this lifting lemma.

The generalized end-to-end theorem has guarded axiom dependencies
`propext`, `Classical.choice`, and `Quot.sound`. It uses no prime-triple
enumeration, `native_decide`, custom axioms, or `sorry`.

## Reduction to an 86-formula catalog

Let `C` be any molecule (`IsMolecule C`) whose atoms all have element `3`, `5`, or `7`.

- If two atoms of `C` share a line, they have the same point set, so by identical-atom isolation `C` is one of the three two-atom dimers `D3 = (2,0,0)`, `D5 = (0,2,0)`, or `D7 = (0,0,2)`.
- Otherwise, `C` aligns injectively to coordinate lines on the CRT grid `Z3 × Z5 × Z7` and satisfies the parity parameterization of [CHEMISTRY.md](CHEMISTRY.md#parity-parameterization). For all three elements present, the 96 normalized weight profiles `(a, b, c) ∈ {0,1} × {0..5} × {0..7}` yield 80 connected formulas; when an element is absent, connectedness confines `C` to a single coordinate slice, yielding only the three binaries `M35`, `M37`, `M57`.

Together these give the complete 86-formula catalog: 80 ternary, 3 binary, and 3 dimer formulas.

## Constructive batch proof

For each feed pair, starting with those two species and repeatedly applying balanced `2→2` catalog reactions whose inputs are already producible reaches all 86 formulas. Because any finite preparation can be run multiple times on fresh disjoint feed copies (retaining all byproducts), reachability of formulas lifts to explicit finite ordered batches without borrowing intermediates.

| Initial feed species | Three-element targets | Full catalog | Max events in certificates |
|---|---:|---:|---:|
| M35, M37 | 80/80 | 86/86 | 46 |
| M35, M57 | 80/80 | 86/86 | 33 |
| M37, M57 | 80/80 | 86/86 | 22 |

Event counts above are certificate bounds, not minima. All 258 ordered batches are saved in [universal_synthesis.json](chemistry/output/universal_synthesis.json) (generated by [universal_synthesis.py](chemistry/universal_synthesis.py)).

## Lean formalization

`Geometry.every_molecule_with_elements357` in [GeometricSynthesis.lean](lean/CyclicAtoms/GeometricSynthesis.lean) proves the full theorem from the original `IsMolecule` definition in [Defs.lean](lean/CyclicAtoms/Defs.lean): for any `C` with elements in `{3, 5, 7}` and any feed pair `p : Fin 3`, there exist finite initial and final stocks of `Molecule357` connected by a `MolecularChain` of `2→2` element-conserving steps such that `initial` uses only `feedPair357 p` and `C` itself appears in `final`.

Lean independently verifies all 86 grid witnesses (with spanning-tree certificates) and all 258 batch certificates rather than trusting Python. See [PROOF_AUDIT.md](lean/PROOF_AUDIT.md) for module details and axiom dependencies.

## Why byproducts are necessary

Without byproducts, a pure pool of `M35` and `M57` always satisfies `5 n5 = 3 n3 + 7 n7`, which fails for `MAX = (35,14,5)` (`70 ≠ 140`). Allowing molecular byproducts removes this obstruction.

In general, a stock consisting only of `Mpq` and `Mqr` satisfies
`q nq = p np + r nr`. The connected layered molecule
`F(1,0,r) = (qr,(p-1)r,q)` violates this equality by `2qr`.
Thus byproducts are also necessary for the generalized universality statement.

## Reproduce

```sh
python -m chemistry.universal_synthesis
python -m verification.check_universal_synthesis
python -m chemistry.verify
cd lean && lake build
```
