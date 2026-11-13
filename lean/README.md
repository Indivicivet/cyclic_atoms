# Lean formalization

Lean 4.

## Usage

Build with `lake build` in `lean/`. The script `lake_rebuild.bat` does `lake clean` then `lake build`. If the build passes then the proofs are valid (but of course we must verify the statements match!).

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

Not yet formalized: CRT reduction of connected configurations to $(1/L)\mathbb{Z}/\mathbb{Z}$, uniqueness of $K_{q,p}$ for two primes, and linking the geometric slice counts directly from `IsMolecule` to the arithmetic hypotheses of `three_prime_upper_bound` and `four_prime_upper_bound`.

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
The large finite checks use `native_decide`, so the synthesis theorem depends
on Lean's standard `Lean.ofReduceBool` axiom and trusts its evaluator and
compiler. `#print axioms` makes this dependency explicit. There are no
project-specific axioms or `sorry` placeholders; the Boolean factorization
is proved without axioms. The generated data are in
[`CyclicAtoms/Chemistry357Data.lean`](CyclicAtoms/Chemistry357Data.lean).

Run `python -m chemistry.universal_synthesis` from the repository root to
regenerate the certificates and finite Python batches. See
[`UNIVERSAL_SYNTHESIS.md`](../UNIVERSAL_SYNTHESIS.md) for the mathematical proof
and assumptions. In particular, these are formula-level endpoint reactions
with molecular byproducts. The unformalized circle-to-CRT/counting bridge
above also applies here: the Lean theorem does not quantify over the original
geometric `IsMolecule` definition.
