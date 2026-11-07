# Lean 4 status

Build with `lake build` in `lean/`. Zero `sorry`s.

- [`CyclicAtoms/Defs.lean`](CyclicAtoms/Defs.lean): Definitions from [`INTRO.md`](../INTRO.md) (`Phase`, `Atom`, `Config`, `RotEquiv`, `IsChiral`, `BondAdj`, `BondReachable`, `IsConnected`, `IsMolecule`, `HasElement`, `multiplicity`, `size`, `InOutAssignment`, `IsBipartite`).
- [`CyclicAtoms/Theory.lean`](CyclicAtoms/Theory.lean): Three results from [`THEORY.md`](../THEORY.md):
  1. `two_mul_bonds_eq_sumDeg` and `even_sumDeg_of_paired`: $2B = \sum p$, so the degree sum is even.
  2. `identical_atoms_isolated` and `identical_atoms_molecule_only_two`: two atoms with the same point set in a molecule cannot bond to a third atom, so every vertex in the molecule is one of those two.
  3. `three_prime_upper_bound` and `three_prime_construction_twice`: the slice-counting upper bound $N \le pq + (s-1)q + p$ for $s < p < q$ and the 2-incidence property of the layered CRT construction on $\mathbb{Z}_s \times \mathbb{Z}_p \times \mathbb{Z}_q$.
- Not yet formalized: CRT reduction of connected configurations to $(1/L)\mathbb{Z}/\mathbb{Z}$, uniqueness of $K_{q,p}$ for two primes, and linking the geometric slice count $T \le kp$ directly from `IsMolecule` to the arithmetic hypothesis of `three_prime_upper_bound`.
