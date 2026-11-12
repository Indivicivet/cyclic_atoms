# Small closed reactions

Starting with only maximum 3–5–7 molecules, we cannot reach binary products through closed reactions with at most two molecules on either side. This holds for three starting maxima, or any number of them. There is no first step that changes their formulas, even if dimers and every other 3–5–7 molecule are admitted as possible intermediates.

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

## Why maxima cannot start reacting

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
