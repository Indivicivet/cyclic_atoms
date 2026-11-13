# Universal synthesis from any two binary feeds

The claim is true for the closed-endpoint reaction model used in
[CLOSED_CHEMISTRY.md](CLOSED_CHEMISTRY.md), allowing molecular byproducts.
It remains true with **only 2→2 events**. Each of the three possible pairs of
binary feeds can produce a copy of every 3-5-7 molecule.

Here `A = M35 = (5,3,0)`, `B = M37 = (7,0,3)` and
`C = M57 = (0,7,5)`. Tuples count atoms of elements 3, 5 and 7.
An appropriate supply means a finite initial multiset containing only the
chosen two feed species, with no preloaded dimers, catalysts or intermediates.
The final multiset contains the target and may contain other molecules.
Every recorded intermediate is a multiset of molecules.

A primitive event is any element-conserving replacement of one or two molecules
by one or two molecules. This is a definition of allowed endpoint chemistry.
The result does not establish a continuous geometric motion, a bound on bonds
broken inside an event, or the absence of isolated atoms during a physical
implementation of a concerted event.

## Reduction to a finite theorem

Take any molecule containing exactly the elements 3, 5 and 7. Rotate one of its
points to zero. Two points of a p-atom differ by a multiple of 1/p. Following
bonds through the connected molecule therefore puts every point on the
105-site grid. The Chinese remainder theorem identifies this grid with
Z3 × Z5 × Z7, and atoms are full coordinate lines.

No line can occur twice: two identical atoms already pair all their points,
form an isolated dimer, and cannot belong to a molecule using three elements.
Let the Boolean line indicators be A(y,z), B(x,z), C(x,y). Exact occupancy
zero or two is equivalent to

    A(y,z) xor B(x,z) xor C(x,y) = 0.

Fix base coordinates x0,y0,z0 and set

    alpha(x) = B(x,z0) xor B(x0,z0)
    beta(y)  = C(x0,y)
    gamma(z) = B(x0,z).

The parity equation at the base slices gives, at every coordinate,

    A(y,z) = beta(y) xor gamma(z)
    B(x,z) = alpha(x) xor gamma(z)
    C(x,y) = alpha(x) xor beta(y).

This factorization is proved for arbitrary index types by
`parity_factorization` in [Chemistry.lean](lean/CyclicAtoms/Chemistry.lean).
Complementing all three bit lists changes none of the indicators. Since the
alpha list has length three, complement if necessary to make its number of
ones a equal to 0 or 1. Let b and c count ones in beta and gamma. Then

    n3 = b(7-c) + (5-b)c
    n5 = a(7-c) + (3-a)c
    n7 = a(5-b) + (3-a)b,

where a ∈ {0,1}, b ∈ {0,...,5}, c ∈ {0,...,7}. These formulas simply count
pairs of unequal bits. Thus every target occurs among 96 weight profiles.
Coordinate permutations take any bit lists with the same weights to the
canonical lists; these permutations preserve the bond graph. The enumeration
therefore checks connectivity for every profile, not a sample of geometries.
Exactly 80 profiles give connected molecules using all three elements, with
80 distinct formulas. Adding A, B, C and the three identical-atom dimers gives
the 86-species reaction catalog.

## Finite constructive proof

For each chosen feed pair, start with those two species. Whenever all inputs
of a balanced catalog reaction are already producible, mark its outputs
producible. Continue until no new species appear. All 86 species are reached
from each pair.

This support argument is valid despite consuming reactants: any finite
preparation can be repeated on fresh disjoint supplies. To obtain two copies
of an intermediate, run its preparation twice. To prepare two different
inputs, run their preparations on disjoint supplies and retain all byproducts.
No intermediate is borrowed. The generator goes further and expands these
arguments into finite, ordered batches. Its replay checks multiplicity, each
consumption and production, and the final target copy.

| Initial feed species | Three-element targets reached | All catalog species reached | Largest number of events in the supplied certificates |
|---|---:|---:|---:|
| M35, M37 | 80/80 | 86/86 | 46 |
| M35, M57 | 80/80 | 86/86 | 33 |
| M37, M57 | 80/80 | 86/86 | 22 |

These event counts are bounds for these particular certificates, not minima.
Every supplied event is 2→2. The proof needs neither 1→2 nor 2→1 reactions.
The explicit initial stocks, ordered reactions and final stocks for all
258 feed-pair/target combinations are in
[universal_synthesis.json](chemistry/output/universal_synthesis.json).
[universal_synthesis.py](chemistry/universal_synthesis.py) regenerates them.

## What Lean checks

[Chemistry.lean](lean/CyclicAtoms/Chemistry.lean) defines molecular formulas,
balanced small reactions, finite stocks, multiplicity-sensitive consumption,
and execution. `Synthesizable` means that an explicit finite batch passes
these checks, starting only with the selected feeds and ending with the target.
It also defines exact paired/connected witnesses on the 105-site grid.

[Chemistry357.lean](lean/CyclicAtoms/Chemistry357.lean) checks the generated
[data](lean/CyclicAtoms/Chemistry357Data.lean) and proves validity of catalog witnesses, all 258 batch
certificates, coverage of the positive three-element parity formulas, and
`every_parity_formula_synthesizable357`. The large finite checks use
`native_decide`. Consequently the proof depends on Lean's standard
`Lean.ofReduceBool` axiom and trusts Lean's evaluator and compiler for those
checks. It is not a pure kernel-reduction proof. There are no project-specific
axioms or `sorry` placeholders. `#print axioms` in the module reports the
dependency explicitly. The Python search is not trusted by this proof: Lean
recomputes the validity of the supplied data. The general Boolean
factorization uses ordinary kernel-checked proofs and no axioms.

There is a formalization boundary. The original rational-circle `IsMolecule`
definition has not yet been connected to the CRT/parity count formulas in
Lean. The mathematical reduction above supplies that step on paper. Thus the
Lean result is the finite parity-formula synthesis theorem, together with the
general Boolean factorization, rather than an end-to-end theorem quantified
over the original `IsMolecule`. This is also the existing CRT gap documented
in [lean/README.md](lean/README.md).

## Why the byproduct condition matters

If the desired final stock must contain only target copies, the assertion is
false. For example, any stock of A and C satisfies

    5 n5 = 3 n3 + 7 n7,

whereas MAX = (35,14,5) has 70 on the left and 140 on the right. No nonzero
number of MAX copies can be the sole product of A and C. Molecular byproducts
remove this obstruction. They are essential to the theorem proved here.

## Reproduce

From the repository root:

```powershell
python -m chemistry.universal_synthesis
python -m verification.check_universal_synthesis
python -m chemistry.verify
cd lean
lake build
```
