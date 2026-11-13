# Small closed reactions

For minimum-length routes from binary feedstocks, see [SYNTHESIS.md](SYNTHESIS.md). The event minima for supplies (M35,M37), (M35,M57), (M37,M57), and all three are 11, 7, 16, and 7. The corresponding minimum numbers of distinct reaction types are 7, 4, 7, and 4, with molecular byproducts allowed.

A maximum 3–5–7 molecule can be an output of a nontrivial 2→2 reaction: the complete catalog contains 29 such formula channels. The smallest example is `M35 + T(30,13,5) → Tmax + D5`, with sizes `8 + 48 → 54 + 2`.

The separate obstruction proved below concerns starting with only maxima. It does not exclude forming a maximum from other molecules, or reacting a maximum with a different partner.

## What "no free atoms" requires

An open bonded fragment is not a free atom, but it is not a molecule either. Allowing bonded open fragments while forbidding isolated atoms is weaker than requiring every intermediate state to consist entirely of molecules. The 140-cut construction violates both restrictions at some intermediate states.

With our original separate cut and join operations, requiring every state to be closed prevents nontrivial chemistry. Cutting a connected molecule exposes sites. Superposing closed molecules cannot form new bonds without occupancy exceeding two. Rotating whole molecules preserves their structures.

An instantaneous 1→2, 2→1 or 2→2 event therefore needs an additional concerted operation: old bonds break and new bonds form in one event, with closed configurations before and after. There is no recorded open intermediate.

For the enumeration here, we use the most permissive endpoint model: two collections of existing molecules with the same atom inventory give a candidate channel. This does not establish continuous motion or a mechanism avoiding isolated atoms at every instant under additional dynamics. Restrictions on simultaneous motions or retained fragments could remove channels. The impossibility result for maxima survives those restrictions because even this permissive model is blocked.

## The small reaction candidates

Write `T(a,b,c)` for formula `3_a 5_b 7_c`. The arguments are atom counts, not coordinate-bit weights. Write `M35 = T(5,3,0)`, `M37 = T(7,0,3)`, and `Dp` for a p-dimer.

Among molecules with elements contained in {3,5,7}, there are exactly two distinct 1↔2 formula equations:

$$
T(18,12,6)\ \rightleftharpoons\ M35+T(13,9,6),
$$

$$
T(22,12,6)\ \rightleftharpoons\ M35+T(17,9,6).
$$

Their reverses give the 2→1 cases. Every molecule in these equations has an exact checked geometric witness.

There are 1,657 nontrivial unordered 2↔2 formula equations. One is the earlier fusion reaction considered as a concerted event:

$$
M35+M37\ \rightleftharpoons\ T(10,3,3)+D3.
$$

The extracted 3-atoms leave as an already bonded dimer in this description. The earlier sequential six-cut construction exposed those atoms; it is not a proof of a path with no free atoms. The concerted description specifies closed endpoints and does not supply a continuous mechanism.

The complete catalog has 86 molecular formulas: 80 using all three elements, three binary formulas and three dimer formulas. Completeness follows from the parity classification in [CHEMISTRY.md](CHEMISTRY.md). Connectivity and double occupancy are checked for every witness. We group singleton and unordered pair inventories by their element counts and match equal inventories. Equations with the same formula multiset on both sides are excluded. Geometric isomers and formula-preserving isomerizations are not counted separately.

## Two molecules producing a maximum

Here are four of the 29 nontrivial formula channels. The notation is `T(a,b,c) = 3_a 5_b 7_c`.

| Reactants | Products | Atom counts |
|---|---|---|
| `M35 + T(30,13,5)` | `Tmax + D5` | `8 + 48 → 54 + 2` |
| `T(16,9,7) + T(19,12,3)` | `Tmax + M57` | `32 + 34 → 54 + 12` |
| `2 T(20,11,5)` | `Tmax + T(5,8,5)` | `36 + 36 → 54 + 18` |
| `2 T(25,12,5)` | `Tmax + T(15,10,5)` | `42 + 42 → 54 + 30` |

The first achieves the smallest possible total input size, 56: the second output must contain at least two atoms. It is the only formula channel producing a maximum plus a dimer. All 29 channels and exact witnesses are saved under `maximum_as_product` in the JSON output.

The first also has an exact ten-bond exchange construction. In CRT coordinates, `T(30,13,5)` has six full z-slices and one exceptional 5-atom in the remaining slice. Place M35 in that remaining slice. The supports intersect precisely in that exceptional 5-atom's five points, which also form one of M35's 5-atoms.

Splice out those two 5-atoms. Their ten old bonds are replaced by five cross-bonds between the remaining fragments and five parallel bonds between the extracted atoms. The products are exactly the maximum and D5. The maximum retains 100 original bonds across the two reactants. In a concerted description the extracted atoms form their dimer in the same event; a sequential cut-first realization would expose them and would not satisfy a no-free-atoms requirement.

`maximum_exchange()` in the enumeration script constructs and verifies the exact endpoint geometry. The other 28 entries are checked balanced endpoint candidates; no particular low-cut mechanism is asserted for them.

## Why a collection of only maxima cannot start changing

Let `Tmax = T(35,14,5)`, with 54 atoms, the maximum molecular size for these elements.

Two maxima contain 108 atoms. One output molecule has at most 54 atoms, ruling out 2→1. With two output molecules, each must have 54 atoms. The only molecular formula of size 54 in the complete catalog is `(35,14,5)`. Thus a 2→2 event only produces two maxima again. Geometric isomerization leaves this formula-level obstruction intact.

A single maximum cannot split into two molecules either. This follows from the parity count identities, which give all possibilities having at most five 7-atoms:

| Number of 7-atoms | Possible molecular formulas |
|---:|---|
| 0 | D3, D5, M35 |
| 2 | D7 |
| 3 | `T(7+3c,3c,3)`, integer `0 ≤ c ≤ 7` |
| 5 | `T(5c,7+c,5)`, integer `0 ≤ c ≤ 7` |

There are no possibilities with one or four 7-atoms. To derive the table, complement the coordinate bits so the 3-coordinate weight a is 0 or 1. Then `n7 = 3b` if a=0 and `n7 = 5+b` if a=1. Substitution into the other count identities gives the displayed families. The zero-7 cases are the elementary one- and two-element molecules.

Two products containing five 7-atoms must distribute them as 5+0 or 3+2:

- For 5+0, subtract D3, D5 or M35 from Tmax. The remainders are `(33,14,5)`, `(35,12,5)` or `(30,11,5)`. None has the required form `(5c,7+c,5)`.
- For 3+2, the second molecule must be D7. The other would be `(35,14,3)`. Its first count requires `7+3c=35`, with no integer c.

So 1→2 is impossible. A 1→1 event preserves the maximum formula too. If a state contains only maxima, every small closed step therefore outputs only maxima. Induction rules out reaching binaries:

$$
3T_{\max}\ \not\longrightarrow\ 14M35+5M37
\quad\text{by closed steps with at most two inputs and two outputs.}
$$

This assumes no additional starting reagents or borrowed catalysts. Adding them changes the reachability problem. Allowing open fragments or larger concerted events also changes it. This result does not identify the smallest larger event that could unlock a sequence.

## Reproduce

```sh
python -m chemistry.closed_reactions
python -m chemistry.verify
```

[closed_reactions.py](chemistry/closed_reactions.py) writes all formulas, exact witnesses and candidate channels to [closed_reactions.json](chemistry/output/closed_reactions.json). Verification checks every witness and balanced equation, the split channels, and the absence of a formula-changing first step from one or two maxima.
