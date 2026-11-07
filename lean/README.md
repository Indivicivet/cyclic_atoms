# Lean formalization

Lean 4.

## Usage

Build with `lake build` in `lean/`. The script `lake_rebuilt.bat` just does `lake clean` then `lake build`. If the build passes then the proofs are valid (but of course we must verify the statements match!).

## Definitions

[`CyclicAtoms/Defs.lean`](CyclicAtoms/Defs.lean)

Definitions from [`INTRO.md`](../INTRO.md) (`Phase`, `Atom`, `Config`, `RotEquiv`, `IsChiral`, `BondAdj`, `BondReachable`, `IsConnected`, `IsMolecule`, `HasElement`, `multiplicity`, `size`, `InOutAssignment`, `IsBipartite`).

## Theory:

[`CyclicAtoms/Theory.lean`](CyclicAtoms/Theory.lean)

Results from [`THEORY.md`](../THEORY.md):
  1. `two_mul_bonds_eq_sumDeg` and `even_sumDeg_of_paired`: $2B = \sum p$, so the degree sum is even.
  2. `identical_atoms_isolated` and `identical_atoms_molecule_only_two`: two atoms with the same point set in a molecule cannot bond to a third atom, so every vertex in the molecule is one of those two.
  3. `three_prime_upper_bound` and `three_prime_construction_twice`: the slice-counting upper bound $N \le pq + (s-1)q + p$ for $s < p < q$ and the 2-incidence property of the layered CRT construction on $\mathbb{Z}_s \times \mathbb{Z}_p \times \mathbb{Z}_q$.
  4. `four_prime_slice_bound`, `four_prime_column_bound`, `validColumns_aggregate`, `four_prime_deficit_bound`, `four_prime_upper_bound`, `four_prime_upper_bound_of_columns`, and `four_prime_construction_twice`: the slice and column-counting upper bound $N \le pqr + (s-1)qr + (p-1)r + q$ for $s < p < q < r$ and the 2-incidence property of the layered CRT construction on $\mathbb{Z}_s \times \mathbb{Z}_p \times \mathbb{Z}_q \times \mathbb{Z}_r$.

Not yet formalized: CRT reduction of connected configurations to $(1/L)\mathbb{Z}/\mathbb{Z}$, uniqueness of $K_{q,p}$ for two primes, and linking the geometric slice counts directly from `IsMolecule` to the arithmetic hypotheses of `three_prime_upper_bound` and `four_prime_upper_bound`.
