# End-to-end synthesis theorem

The public theorem is `CyclicAtoms.Geometry.every_molecule_with_elements357` in [GeometricSynthesis.lean](CyclicAtoms/GeometricSynthesis.lean) (with `every_molecule_with_exact_elements357` as a corollary for the three-element case), built directly on [Defs.lean](CyclicAtoms/Defs.lean).

```lean
theorem every_molecule_with_elements357 (C : Config) (hm : IsMolecule C)
    (helements : ∀ q : Nat, C.HasElement q → q = 3 ∨ q = 5 ∨ q = 7)
    (p : Fin 3) :
    ∃ initial final : List Molecule357,
      (∀ m ∈ initial, m.formula ∈ feedPair357 p) ∧
      MolecularChain initial final ∧ ∃ m ∈ final, m.config = C
```

| `p` | Permitted initial formulas (`feedPair357 p`) |
|---|---|
| 0 | `M35 = (5,3,0)`, `M37 = (7,0,3)` |
| 1 | `M35 = (5,3,0)`, `M57 = (0,7,5)` |
| 2 | `M37 = (7,0,3)`, `M57 = (0,7,5)` |

## Reaction model

`Molecule357` pairs a `Config` with proofs of `IsMolecule config` and `Elements357 config`. Every stock entry has its own angular frame. `MolecularStep.replace` swaps two molecules in the stock for two molecules with equal element counts (`MolecularStep.conserves` / `MolecularChain.conserves` prove conservation of `stockCount stock q` for every `q : Nat`). These are balanced `2→2` closed-endpoint steps; continuous paths and internal bond-break bounds are not modeled.

## Proof structure

1. **Circle to parity classification** ([Circle.lean](CyclicAtoms/Circle.lean), [GridLines.lean](CyclicAtoms/GridLines.lean), [GridAlignment.lean](CyclicAtoms/GridAlignment.lean), [Counting357.lean](CyclicAtoms/Counting357.lean)): `phase_equiv_iff_circle` identifies `Phase.Equiv` with equality in `ℝ/ℤ`; connectedness aligns `C` to a coset of the 105-grid (`connected_grid_alignment`), and `lineFor_orbit` identifies atoms with coordinate lines on `Z3 × Z5 × Z7`. If two atoms share a line, `identical_atoms_molecule_only_two` forces `C` to be a dimer (`D3`, `D5`, or `D7`). Otherwise `g.lines` is injective, exact pairing yields the XOR parity equation (`GridAlignment.parity`), `parity_factorization` factors it into `3 + 5 + 7` bits, and connectedness bounds single-slice counts when an element is missing (`no_element_3/5/7_bounds`).
2. **Catalog realization and execution** ([Chemistry.lean](CyclicAtoms/Chemistry.lean), [Chemistry357.lean](CyclicAtoms/Chemistry357.lean), [GridWitness.lean](CyclicAtoms/GridWitness.lean), [GeometryWitness357.lean](CyclicAtoms/GeometryWitness357.lean), [GeometricSynthesis.lean](CyclicAtoms/GeometricSynthesis.lean)): `GridAlignment.isMolecule` proves `IsMolecule` for all 86 catalog witnesses from `FinitePairing` and parent/rank spanning-tree certificates (`GeometryWitnessData.lean`). `execute_geometric` lifts checked formula certificates in `Chemistry357Data.lean` to `MolecularChain`, using `realizeFor` to instantiate `C`'s formula with `C` itself.

## Toolchain, axioms, and regeneration

Pinned to Lean 4.19.0 and Mathlib v4.19.0. To build and verify guarded `#print axioms` checks:

```sh
cd lean
lake update   # once, to fetch dependencies
lake build
lake env lean CyclicAtoms/GeometricSynthesis.lean
```

Guarded axiom dependencies for `every_molecule_with_elements357`:

```text
propext, Classical.choice, Lean.ofReduceBool, Quot.sound
```

`Lean.ofReduceBool` comes from `native_decide` on the finite CRT, counting, witness, and certificate checks; there are no custom axioms or `sorry`s, and the Python generator (`python -m chemistry.universal_synthesis`) is not trusted by the proof.

## Generalized formula synthesis

[`UniversalSynthesis.lean`](CyclicAtoms/UniversalSynthesis.lean) adds a separate
parameterized theorem, `CyclicAtoms.UniversalSynthesis.universal_synthesis`.
For `p,q ≥ 3`, `r ≥ 2`, and any of the three binary feed pairs, it produces
finite initial and final stocks and an ordered `Chain` of balanced `2→2`
steps containing a requested `Valid p q r` formula. `Valid` explicitly lists
the three dimers, the three binaries, and all bounded parity profiles with
three positive counts. It is a formula predicate, not `IsMolecule`.

The proof uses affine midpoint reactions, a boundary-to-interior reaction,
coordinate permutations, and induction on finite production trees.
`Reachable.batch` prepares the two inputs on independent fresh feed supplies
before reacting them, preserving all byproducts and input multiplicities.
`Chain.conserves` and `Chain.card_eq` verify element conservation and the
constant number of molecules.

The guarded axiom list is `propext, Classical.choice, Quot.sound`; this module
uses neither `native_decide` nor unproved axioms. It does **not** generalize
the circle-to-parity classification or catalog realization from the original
`Config` / `IsMolecule` definitions. Those arbitrary-prime geometric arguments
are given in [UNIVERSAL_SYNTHESIS.md](../UNIVERSAL_SYNTHESIS.md), while the
existing Lean end-to-end bridge continues to cover `{3,5,7}` only.
