# End-to-end synthesis theorem

The general theorem is `CyclicAtoms.GeneralSynthesis.every_molecule_with_elements` in [GeneralSynthesis.lean](CyclicAtoms/GeneralSynthesis.lean), built directly on the unchanged definitions in [Defs.lean](CyclicAtoms/Defs.lean).

```lean
theorem every_molecule_with_elements (p q r : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (C : Config) (hm : IsMolecule C)
    (helements : ∀ e : ℕ, C.HasElement e → e = p ∨ e = q ∨ e = r)
    (pair : Fin 3) :
    ∃ initial final : Multiset (Molecule p q r),
      (∀ m ∈ initial, m.formula ∈ feedPair p q r pair) ∧
      MolecularChain p q r initial final ∧ ∃ m ∈ final, m.config = C
```

| `pair` | Permitted initial formulas (`feedPair p q r pair`) |
|---|---|
| 0 | `M(p,q) = (q,p,0)`, `M(p,r) = (r,0,p)` |
| 1 | `M(p,q) = (q,p,0)`, `M(q,r) = (0,r,q)` |
| 2 | `M(p,r) = (r,0,p)`, `M(q,r) = (0,r,q)` |

## Reaction model and catalog equivalence

`Molecule p q r` pairs a `Config` with proofs of `IsMolecule config` and `Elements p q r config`. Each `MolecularStep.replace` swaps two molecules in the multiset stock for two molecules with equal element multiplicities (`MolecularStep.conserves` proves conservation of every `e : ℕ`; `MolecularChain.card_eq` proves molecule count is constant). These are closed-endpoint `2→2` steps; continuous trajectories and bond-break bounds are not modeled.

`GeneralSynthesis.valid_iff_original_molecule` proves that `Valid p q r f` holds iff there exists an original `IsMolecule` configuration over `{p, q, r}` with formula `f`.

## Module structure

1. **Circle geometry and classification** ([PrimeGeometry.lean](CyclicAtoms/PrimeGeometry.lean), [ElementCounting.lean](CyclicAtoms/ElementCounting.lean), [PrimeGrid.lean](CyclicAtoms/PrimeGrid.lean), [PrimeGridCounting.lean](CyclicAtoms/PrimeGridCounting.lean), [PrimeGridClassification.lean](CyclicAtoms/PrimeGridClassification.lean), [OriginalClassification.lean](CyclicAtoms/OriginalClassification.lean)): Aligns `C` to the `pqr`-grid via CRT; non-injective lines yield an isolated dimer (`Alignment.dimer_of_not_injective`), and injective lines yield `Paired` + `Connected`, hence `Valid p q r`.
2. **Realization and synthesis lifting** ([PrimeGridRealization.lean](CyclicAtoms/PrimeGridRealization.lean), [PrimeMoleculeWitness.lean](CyclicAtoms/PrimeMoleculeWitness.lean), [UniversalSynthesis.lean](CyclicAtoms/UniversalSynthesis.lean), [FormulaPermutations.lean](CyclicAtoms/FormulaPermutations.lean), [MolecularSynthesis.lean](CyclicAtoms/MolecularSynthesis.lean)): Constructs `IsMolecule` witnesses for every `Valid` formula, proves formula-level `2→2` synthesis for any prime ordering (including `2` in any position), and lifts batches via `synthesis_of_classification_and_realization`, instantiating `C`'s formula with `C` itself.

## `{3, 5, 7}` explicit-certificate specialization

`CyclicAtoms.Geometry.every_molecule_with_elements357` in [GeometricSynthesis.lean](CyclicAtoms/GeometricSynthesis.lean) (with `every_molecule_with_exact_elements357` as a three-element corollary) gives the same conclusion for `{3, 5, 7}` using explicit `native_decide`-checked grid witnesses and 258 batch certificates ([Chemistry.lean](CyclicAtoms/Chemistry.lean), [Chemistry357.lean](CyclicAtoms/Chemistry357.lean), [Circle.lean](CyclicAtoms/Circle.lean), [GridLines.lean](CyclicAtoms/GridLines.lean), [GridAlignment.lean](CyclicAtoms/GridAlignment.lean), [Counting357.lean](CyclicAtoms/Counting357.lean), [GridWitness.lean](CyclicAtoms/GridWitness.lean), [GeometryWitness357.lean](CyclicAtoms/GeometryWitness357.lean)).

## Toolchain and axioms

Pinned to Lean 4.19.0 and Mathlib v4.19.0:

```sh
cd lean
lake update   # once, to fetch dependencies
lake build
lake env lean CyclicAtoms/GeneralSynthesis.lean
lake env lean CyclicAtoms/GeometricSynthesis.lean
```

Guarded `#print axioms` dependencies (no custom axioms or `sorry`s):

- `GeneralSynthesis.every_molecule_with_elements` and `valid_iff_original_molecule`: `propext, Classical.choice, Quot.sound` (no `native_decide`).
- `Geometry.every_molecule_with_elements357`: `propext, Classical.choice, Lean.ofReduceBool, Quot.sound` (`Lean.ofReduceBool` from `native_decide`).
