# Small closed reactions

For minimum-length routes from binary feedstocks, see [SYNTHESIS.md](SYNTHESIS.md). Event minima for supplies `(M35,M37)`, `(M35,M57)`, `(M37,M57)`, and all three are 11, 7, 16, and 7; minimum distinct reaction types are 7, 4, 7, and 4 (with molecular byproducts allowed).

A maximum 3-5-7 molecule can still be produced by a nontrivial `2→2` step: 29 catalog channels yield `Tmax`, starting at `M35 + T(30,13,5) → Tmax + D5` (sizes `8 + 48 → 54 + 2`). The obstruction proved below only rules out starting from maxima alone.

## Closed-state model

Under separate cut and join operations, keeping every intermediate state closed forbids all chemistry: cutting a connected molecule opens sites, superposing closed molecules exceeds occupancy two, and rotating whole molecules leaves them unchanged.

We therefore allow concerted `1→2`, `2→1`, and `2→2` steps whose inputs and outputs are closed molecules with matching element counts. Because this endpoint model imposes no continuous motion or low-cut constraints, the impossibility result for maxima also holds under any stricter dynamics.

## The small reaction candidates

Write `T(a,b,c)` for `3_a 5_b 7_c` (atom counts, not coordinate-bit weights), `M35 = T(5,3,0)`, `M37 = T(7,0,3)`, and `Dp` for a `p`-dimer.

Among molecules with elements in `{3,5,7}`, there are exactly two `1↔2` formula equations (their reverses give the `2→1` cases), each with a checked geometric witness:

$$
T(18,12,6)\ \rightleftharpoons\ M35+T(13,9,6),
$$

$$
T(22,12,6)\ \rightleftharpoons\ M35+T(17,9,6).
$$

There are 1,657 nontrivial unordered `2↔2` equations, including the concerted version of the six-cut fusion reaction where the extracted 3-atoms leave directly as a dimer:

$$
M35+M37\ \rightleftharpoons\ T(10,3,3)+D3.
$$

The catalog has 86 formulas (80 ternary, 3 binary, 3 dimer), complete by the parity classification in [CHEMISTRY.md](CHEMISTRY.md). Matching singleton and unordered pair inventories by element count—excluding trivial identities and without distinguishing geometric isomers—yields these channels.

## Two molecules producing a maximum

Four of the 29 `2→2` channels that output `Tmax`:

| Reactants | Products | Atom counts |
|---|---|---|
| `M35 + T(30,13,5)` | `Tmax + D5` | `8 + 48 → 54 + 2` |
| `T(16,9,7) + T(19,12,3)` | `Tmax + M57` | `32 + 34 → 54 + 12` |
| `2 T(20,11,5)` | `Tmax + T(5,8,5)` | `36 + 36 → 54 + 18` |
| `2 T(25,12,5)` | `Tmax + T(15,10,5)` | `42 + 42 → 54 + 30` |

The first has the minimum total input size (56, since the second product must have at least two atoms) and is the only channel yielding `Tmax` plus a dimer.

It also has a 10-bond exchange construction. In CRT coordinates, `T(30,13,5)` has six full `z`-slices and one exceptional 5-atom in the seventh. Placing `M35` in that slice aligns one of its 5-atoms with the exceptional 5-atom. Splicing out both 5-atoms replaces their ten bonds with five cross-bonds and five dimer bonds, giving `Tmax` (retaining 100 original bonds) and `D5`. `maximum_exchange()` constructs this witness; the other 28 entries in `maximum_as_product` are balanced endpoint channels.

## Why a collection of only maxima cannot start changing

Let `Tmax = T(35,14,5)` (54 atoms, the maximum molecular size for `{3,5,7}`).

Two maxima have 108 atoms. Since one molecule has at most 54 atoms, `2→1` is impossible, and `2→2` forces two 54-atom products. The only 54-atom formula in the catalog is `T(35,14,5)`, so `2→2` only returns two maxima.

A single maximum cannot split (`1→2`) either. Complementing coordinate bits so `a in {0,1}` gives `n7 = 3b` (`a=0`) or `n7 = 5+b` (`a=1`), which yields all catalog formulas with at most five 7-atoms:

| Number of 7-atoms | Possible molecular formulas |
|---:|---|
| 0 | D3, D5, M35 |
| 2 | D7 |
| 3 | `T(7+3c,3c,3)`, integer `0 ≤ c ≤ 7` |
| 5 | `T(5c,7+c,5)`, integer `0 ≤ c ≤ 7` |

Splitting five 7-atoms into two products requires `5+0` or `3+2`:

- `5+0`: subtracting `D3`, `D5`, or `M35` from `Tmax` leaves `(33,14,5)`, `(35,12,5)`, or `(30,11,5)`, none of the form `(5c,7+c,5)`.
- `3+2`: the second product must be `D7`, leaving `(35,14,3)`, which requires `7+3c = 35` (no integer solution).

Thus `1→1`, `1→2`, and `2→2` steps on maxima only output maxima, so by induction:

$$
3T_{\max}\ \not\longrightarrow\ 14M35+5M37
\quad\text{by closed steps with at most two inputs and two outputs.}
$$

This assumes no extra reagents, catalysts, open intermediates, or larger concerted steps.

## Reproduce

```sh
python -m chemistry.closed_reactions
python -m chemistry.verify
```

[closed_reactions.py](chemistry/closed_reactions.py) writes all formulas, witnesses, and channels to [closed_reactions.json](chemistry/output/closed_reactions.json).
