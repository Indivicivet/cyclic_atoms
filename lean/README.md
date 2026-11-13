# Lean formalization

Lean 4.19.0 with Mathlib v4.19.0, pinned by `lean-toolchain`, `lakefile.lean`, and `lake-manifest.json`. The original definitions in `Defs.lean` are unchanged.

## Usage

Run `lake update` once in `lean/` to fetch dependencies, then `lake build` (or `lake_rebuild.bat` for a clean rebuild). See [PROOF_AUDIT.md](PROOF_AUDIT.md) for the end-to-end theorem statement and axiom audit.

## Definitions and elementary bounds

- [`CyclicAtoms/Defs.lean`](CyclicAtoms/Defs.lean): Definitions from [`INTRO.md`](../INTRO.md) (`Phase`, `Atom`, `Config`, `RotEquiv`, `IsChiral`, `BondAdj`, `BondReachable`, `IsConnected`, `IsMolecule`, `HasElement`, `multiplicity`, `size`, `InOutAssignment`, `IsBipartite`).
- [`CyclicAtoms/Elementary.lean`](CyclicAtoms/Elementary.lean): `2B = Σ p` (`two_mul_bonds_eq_sumDeg`, `even_sumDeg_of_paired`) and isolation of identical atoms (`identical_atoms_isolated`, `identical_atoms_molecule_only_two`).
- [`CyclicAtoms/MaxSize.lean`](CyclicAtoms/MaxSize.lean): Three- and four-prime maximum size upper bounds and layered CRT constructions (`three_prime_upper_bound`, `three_prime_construction_twice`, `four_prime_upper_bound`, `four_prime_construction_twice`). For general element sets, the CRT reduction and uniqueness of $K_{q,p}$ remain unformalized.

## Universal synthesis for `{3, 5, 7}`

The main theorem is `Geometry.every_molecule_with_elements357` in [`CyclicAtoms/GeometricSynthesis.lean`](CyclicAtoms/GeometricSynthesis.lean): any `IsMolecule C` with elements in `{3, 5, 7}` can be formed from any binary feed pair (`M35/M37`, `M35/M57`, or `M37/M57`) via a `MolecularChain` of element-conserving `2→2` molecular replacements (allowing byproducts), producing `C` itself in the final stock.

- [`CyclicAtoms/Chemistry.lean`](CyclicAtoms/Chemistry.lean): Formulas, `2→2` batch execution, finite grid witnesses, and kernel-checked `parity_factorization`.
- [`CyclicAtoms/Chemistry357.lean`](CyclicAtoms/Chemistry357.lean) & [`Chemistry357Data.lean`](CyclicAtoms/Chemistry357Data.lean): `native_decide`-checked grid witnesses for all 86 formulas and 258 synthesis batch certificates (regenerated via `python -m chemistry.universal_synthesis`).
- [`CyclicAtoms/Circle.lean`](CyclicAtoms/Circle.lean), [`GridLines.lean`](CyclicAtoms/GridLines.lean), [`GridAlignment.lean`](CyclicAtoms/GridAlignment.lean), [`Counting357.lean`](CyclicAtoms/Counting357.lean): Circle-to-CRT alignment, injective line exclusion / dimer fallback, parity classification, and single-slice bounds for 2-element molecules.
- [`CyclicAtoms/GridWitness.lean`](CyclicAtoms/GridWitness.lean), [`GeometryWitness357.lean`](CyclicAtoms/GeometryWitness357.lean), [`GeometryWitnessData.lean`](CyclicAtoms/GeometryWitnessData.lean): Spanning-tree certificates proving `IsMolecule` for all 86 catalog witnesses and lifting formula plans to `MolecularChain`.

See [`UNIVERSAL_SYNTHESIS.md`](../UNIVERSAL_SYNTHESIS.md) for the mathematical overview.

## Universal synthesis for arbitrary prime triples

[`CyclicAtoms/UniversalSynthesis.lean`](CyclicAtoms/UniversalSynthesis.lean)
proves `UniversalSynthesis.universal_synthesis`: for all integer dimensions
`p,q ≥ 3`, `r ≥ 2`, every formula in the generalized parity catalog is
reachable from any two binary feeds by a finite sequential batch of balanced
`2→2` replacements, retaining byproducts. Any triple of distinct primes can
be relabeled to satisfy these bounds, including triples containing 2.

This symbolic proof uses no catalog enumeration, `native_decide`, custom
axioms, or `sorry`. `Chain.conserves` proves conservation of each element;
`Chain.card_eq` proves conservation of the number of molecules. Its scope
is the parity formula catalog. The arbitrary-prime geometric classification
and realization are proved in the mathematical overview, but their Lean
bridge to the original `IsMolecule` definition remains specific to 3–5–7.
