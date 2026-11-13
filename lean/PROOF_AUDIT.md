# End-to-end synthesis theorem

The public theorem is `CyclicAtoms.Geometry.every_molecule_with_exact_elements357`
in [GeometricSynthesis.lean](CyclicAtoms/GeometricSynthesis.lean). It starts from
the original definitions in [Defs.lean](CyclicAtoms/Defs.lean), which have not
been changed.

Its mathematical statement is:

> Let C be any molecule whose element set is exactly {3,5,7}. Choose any two
> of M35, M37 and M57. There are finite initial and final multisets of molecules
> such that the initial multiset contains only the chosen feed species, the
> final multiset contains C itself, and the initial multiset transforms into
> the final one by a finite sequence of element-conserving 2→2 replacements.

Byproducts are permitted. No other initial species are supplied.

The actual Lean statement, inside `namespace CyclicAtoms.Geometry`, is:

```lean
theorem every_molecule_with_exact_elements357 (C : Config) (hm : IsMolecule C)
    (helements : ∀ q : Nat, C.HasElement q ↔ q = 3 ∨ q = 5 ∨ q = 7)
    (p : Fin 3) :
    ∃ initial final : List Molecule357,
      (∀ m ∈ initial, m.formula ∈ feedPair357 p) ∧
      MolecularChain initial final ∧ ∃ m ∈ final, m.config = C
```

The feed parameter has precisely these three values:

| p | Permitted initial molecular formulas |
|---|---|
| 0 | M35 = (5,3,0), M37 = (7,0,3) |
| 1 | M35 = (5,3,0), M57 = (0,7,5) |
| 2 | M37 = (7,0,3), M57 = (0,7,5) |

Tuples count atoms of elements 3, 5 and 7. The conclusion identifies the final
configuration with C by literal equality, so it applies to any geometric isomer.
It does not merely produce some other molecule with C's formula.

## Meaning of the reaction statement

`Molecule357` contains a `Config`, a proof of the original `IsMolecule` predicate,
and a proof that every atom has element 3, 5 or 7. Thus every member of every
stock in a `MolecularChain` is an original molecule, including the dimers.
Stock entries have independent angular frames; the stock is not a superposition
of every molecule on a single circle.

`MolecularStep.replace` selects exactly two input molecules and exactly two
output molecules. It requires equality of the total element-count vectors.
The rest of the stock remains present. A list permutation allows the selected
inputs to occur anywhere in the stock. This treats stocks as multisets while
retaining multiplicity: two copies of a molecule are distinct stock entries.

`MolecularStep.conserves` proves equality of the total number of q-atoms for
every natural number q, using `Config.multiplicity`. `MolecularChain.conserves`
propagates this conservation through an entire chain. Counts outside {3,5,7}
are zero because each stock entry carries its element-support proof.

These are the maximally permissive closed-endpoint rules used by the synthesis
search. An arbitrary balanced 2→2 molecular replacement is allowed as one
concerted event. A continuous geometric path, restrictions on bonds broken
inside an event, and the absence of free atoms inside such a path are not part
of this model. No such stronger dynamical result is claimed by the theorem.

## Proof from the original geometry

1. `phase_equiv_iff_circle` identifies the original cross-multiplication and
   remainder definition of `Phase.Equiv` with equality in ℝ/ℤ. Arbitrary
   numerator/denominator representatives are allowed.
2. `circle_point` identifies each atom's increments with multiples of 1/105.
   `bond_grid_difference` and `reachable_grid_difference` propagate this fact
   along the original `BondReachable` walks. `connected_grid_alignment` derives
   one common grid coset from connectedness; grid alignment is not an input.
3. `lineFor_orbit` identifies these finite atom orbits with coordinate lines.
   `aligned_atom_hasPoint` is an equivalence for every original `Phase x`, not
   just the sampled grid points. The explicit CRT map is
   `site x y z = 70*x + 21*y + 15*z mod 105`.
4. `GridAlignment.injective` uses the previously proved identical-atom isolation
   theorem and the presence of three elements. It derives that no two atom
   vertices represent the same line.
5. `GridAlignment.present_partner` transports the original exact-pairing
   condition to the finite lines. `GridAlignment.parity` rules out singleton
   and triple occupancy and proves A(y,z) xor B(x,z) xor C(x,y) = 0.
6. `parity_factorization` yields the three bit lists. `GridAlignment.count`
   proves that the original list multiplicities equal the finite line counts.
   `parityMask_counts` proves the exact weight formulas for every assignment
   of the 3+5+7 bits. `rawParityFormula_normalized` accounts for simultaneous
   bit complementation. No connectivity or counting assumption is added.
7. `original_molecule_parity_formula` consequently produces the normalized
   parity parameters from the original `IsMolecule` and element-set hypotheses.
   The existing finite synthesis certificates then apply to `configFormula C`.

The modules are [Circle](CyclicAtoms/Circle.lean),
[GridLines](CyclicAtoms/GridLines.lean),
[GridAlignment](CyclicAtoms/GridAlignment.lean), and
[Counting357](CyclicAtoms/Counting357.lean).

## Proof that the recipes are geometric molecular reactions

The formula theorem alone would leave a second gap: the formulas used in the
recipes need actual molecular realizations. That gap is closed too.

`lineAtom_points` proves the original point-set semantics of the canonical
circle atoms. `GridAlignment.isMolecule` proves the original infinite-point
pairing and connectedness predicates from finite occupancy and a spanning-tree
certificate. Strictly decreasing parent ranks prove reachability to the root.
`geometric_witness_checks357` checks these conditions for all 86 catalog
witnesses. `catalog_realizable357` therefore supplies original molecules,
with exactly the stated element multiplicities, for every reaction species.
This proof does not assume correctness of the earlier Boolean BFS checker.

`removeOne_perm` and `consume_perm` show that successful checker consumption
actually removes the required multiset of reactants. `formula_beq_true`
proves correctness of the checker's Boolean formula equality. The table is
proved to contain only 2→2 reactions. `execute_geometric` lifts every successful
formula execution to a `MolecularChain` of actual molecules.

The realizer deliberately chooses the requested C whenever its formula occurs.
It preserves formulas, so all reaction balances remain valid and the exact C
occurs among the final products. This proves the final theorem without an
isomer-equivalence assumption.

See [GridWitness](CyclicAtoms/GridWitness.lean),
[GeometryWitness357](CyclicAtoms/GeometryWitness357.lean), and
[GeometricSynthesis](CyclicAtoms/GeometricSynthesis.lean).

## Computation, axioms and reproduction

The proof uses Lean 4.19.0 and Mathlib v4.19.0. Their exact revisions are pinned
in the toolchain and dependency manifest. The root `CyclicAtoms.lean` imports
the end-to-end theorem, so the ordinary default build checks it.

```powershell
cd lean
lake update
lake build
lake env lean CyclicAtoms/GeometricSynthesis.lean
```

The final command checks the public theorems' axiom dependencies against
guarded expectations. The build fails if that list changes:

```text
propext, Classical.choice, Lean.ofReduceBool, Quot.sound
```

There are no project-specific axioms or admitted proof placeholders.
`Lean.ofReduceBool` is the standard dependency of `native_decide`: the finite
checks trust Lean's compiler and evaluator. The argument is therefore not a
pure kernel-reduction proof. The circle algebra and the general soundness
arguments are ordinary proofs; the native computations check finite CRT
identities, bit assignments/counts, catalog witnesses and reaction certificates.

The Python generator is not trusted by the Lean proof. Regenerate recipe and
tree data from the repository root with `python -m chemistry.universal_synthesis`.
The generated [GeometryWitnessData.lean](CyclicAtoms/GeometryWitnessData.lean)
contains parent/rank data, not assumed connectivity proofs. Lean checks the
data and proves that passing those checks implies the original predicates.
