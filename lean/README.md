# Lean formalization

Lean 4.19.0 with Mathlib v4.19.0, pinned by `lean-toolchain`, `lakefile.lean`
and `lake-manifest.json`. The original definitions in `Defs.lean` are unchanged.

## Usage

Run `lake update` once in `lean/` to fetch the pinned dependencies and cached
Mathlib proofs, then build with `lake build`. The script `lake_rebuild.bat`
does `lake clean` then `lake build`. [PROOF_AUDIT.md](PROOF_AUDIT.md) states the
end-to-end synthesis theorem and explains its assumptions and trust boundary.

## Definitions

[`CyclicAtoms/Defs.lean`](CyclicAtoms/Defs.lean)

Definitions from [`INTRO.md`](../INTRO.md) (`Phase`, `Atom`, `Config`, `RotEquiv`, `IsChiral`, `BondAdj`, `BondReachable`, `IsConnected`, `IsMolecule`, `HasElement`, `multiplicity`, `size`, `InOutAssignment`, `IsBipartite`).

## Elementary results

[`CyclicAtoms/Elementary.lean`](CyclicAtoms/Elementary.lean)

Elementary facts from [`THEORY.md`](../THEORY.md):
  1. `two_mul_bonds_eq_sumDeg` and `even_sumDeg_of_paired`: $2B = \sum p$, so the degree sum is even.
  2. `identical_atoms_isolated` and `identical_atoms_molecule_only_two`: two atoms with the same point set in a molecule cannot bond to a third atom, so every vertex in the molecule is one of those two.

## Maximum sizes for three and four primes

[`CyclicAtoms/MaxSize.lean`](CyclicAtoms/MaxSize.lean)

Maximum size bounds and constructions from [`THEORY.md`](../THEORY.md) and [`PROOF_SKETCHES.md`](../PROOF_SKETCHES.md):
  1. `three_prime_upper_bound` and `three_prime_construction_twice`: the slice-counting upper bound $N \le pq + (s-1)q + p$ for $s < p < q$ and the 2-incidence property of the layered CRT construction on $\mathbb{Z}_s \times \mathbb{Z}_p \times \mathbb{Z}_q$.
  2. `four_prime_slice_bound`, `four_prime_column_bound`, `validColumns_aggregate`, `four_prime_deficit_bound`, `four_prime_upper_bound`, `four_prime_upper_bound_of_columns`, and `four_prime_construction_twice`: the slice and column-counting upper bound $N \le pqr + (s-1)qr + (p-1)r + q$ for $s < p < q < r$ and the 2-incidence property of the layered CRT construction on $\mathbb{Z}_s \times \mathbb{Z}_p \times \mathbb{Z}_q \times \mathbb{Z}_r$.

For general element sets, the CRT reduction, uniqueness of $K_{q,p}$ for two
primes, and the link from `IsMolecule` to the general maximum-size arithmetic
hypotheses remain unformalized. The complete reduction and classification for
the particular element set `{3,5,7}` are proved in the modules below.

## Universal synthesis for 3, 5 and 7

[`CyclicAtoms/Chemistry.lean`](CyclicAtoms/Chemistry.lean) defines conserved
formulas, reactions with one or two molecules on each side, and explicit finite
batch execution. Consumption respects multiplicities and requires all inputs
to be present. Initial stock contains only the chosen binary feeds. The module
also defines paired, connected finite grid witnesses and proves the general
Boolean `parity_factorization` theorem.

[`CyclicAtoms/Chemistry357.lean`](CyclicAtoms/Chemistry357.lean) contains
generated certificates for all 86 molecular formulas from each of the three
binary feed pairs. The main theorem is
`every_parity_formula_synthesizable357`: each positive three-element parity
formula is synthesizable from any feed pair. `catalog_witnesses357` checks
paired occupancy and connectivity for the species used by the reactions.
The large finite checks use `native_decide` and trust Lean's evaluator and
compiler through its standard `Lean.ofReduceBool` axiom. The generated data are in
[`CyclicAtoms/Chemistry357Data.lean`](CyclicAtoms/Chemistry357Data.lean).

Run `python -m chemistry.universal_synthesis` from the repository root to
regenerate the certificates and finite Python batches. See
[`UNIVERSAL_SYNTHESIS.md`](../UNIVERSAL_SYNTHESIS.md) for the mathematical proof
and assumptions.

## From the original circle definition to actual molecular stocks

The main public theorem is `Geometry.every_molecule_with_exact_elements357`
in [`GeometricSynthesis.lean`](CyclicAtoms/GeometricSynthesis.lean). Its
premises are the original `IsMolecule C` and the exact element set `{3,5,7}`.
For any binary feed pair, its conclusion supplies finite initial and final
stocks of original molecules, a chain of 2→2 molecular reactions, and the
exact requested `C` in the final stock. Molecular byproducts are permitted.
`MolecularChain.conserves` proves conservation of every element.

The proof is split as follows:

- [`Circle.lean`](CyclicAtoms/Circle.lean): the original phase equivalence is
  equality in ℝ/ℤ; connectedness derives alignment to a coset of the 105-grid.
- [`GridLines.lean`](CyclicAtoms/GridLines.lean): finite CRT coordinates and
  the exact point-set identification of aligned atoms with coordinate lines.
- [`GridAlignment.lean`](CyclicAtoms/GridAlignment.lean): identical-line
  exclusion and the parity equation from the original exact-pairing condition.
- [`Counting357.lean`](CyclicAtoms/Counting357.lean): preservation of original
  list multiplicities, exact XOR counts, and normalized parity classification.
- [`GridWitness.lean`](CyclicAtoms/GridWitness.lean) and
  [`GeometryWitness357.lean`](CyclicAtoms/GeometryWitness357.lean): checked
  occupancy and spanning trees imply the original `IsMolecule` predicate for
  every catalog witness.
- [`GeometricSynthesis.lean`](CyclicAtoms/GeometricSynthesis.lean): executable
  formula batches lift to actual molecular stocks and the specified isomer.

There are no project-specific axioms or admitted proofs. The end-to-end theorem
uses the standard classical/quotient axioms and `Lean.ofReduceBool`; the source
guards its full axiom dependencies. The reactions are balanced instantaneous
endpoint replacements. No continuous motion or bound on broken bonds is asserted.
