# Universal synthesis from any two binary feeds

Under the closed-endpoint reaction model from [CLOSED_CHEMISTRY.md](CLOSED_CHEMISTRY.md) with molecular byproducts allowed, any molecule whose elements lie in a triple of distinct primes `{p, q, r}` can be formed from an initial pool containing only any two of the three binary molecules

$$
M_{pq}=(q,p,0),\qquad M_{pr}=(r,0,p),\qquad M_{qr}=(0,r,q),
$$

using only element-conserving `2→2` molecular steps (including triples containing `2`, and without preloaded dimers, catalysts, or borrowed intermediates).

## Proof for any three distinct primes

Let `Dp = (2,0,0)`, `Dq = (0,2,0)`, and `Dr = (0,0,2)` be the three dimers. Using the [parity parameterization](CHEMISTRY.md#parity-parameterization) with weights `0 ≤ a ≤ p`, `0 ≤ b ≤ q`, and `0 ≤ c ≤ r`, write

$$
F(a,b,c)=\bigl(b(r-c)+(q-b)c,\ a(r-c)+(p-a)c,\ a(q-b)+(p-a)b\bigr).
$$

### Classification and realization

Every molecule (`IsMolecule C`) with elements in `{p, q, r}` aligns by connectedness to a translate of the `pqr` circle grid, identified via CRT with `Zp × Zq × Zr`.

- If two atoms coincide on the same line, identical-atom isolation forces `C` to be one of the three two-atom dimers `Dp`, `Dq`, or `Dr`.
- Otherwise, each coordinate line appears at most once and exact pairing gives `A(y,z) xor B(x,z) xor C(x,y) = 0`, whose solution is the parity parameterization. If one element is absent, connectedness confines `C` to a single coordinate slice, giving `Mpq`, `Mpr`, or `Mqr`.

Conversely, every profile `F(a,b,c)` with all three counts positive gives a connected, doubly occupied grid configuration. Partitioning the present lines into the six classes `A01`, `B01`, `C01`, `A10`, `B10`, `C10` by their fixed coordinate bits, bonds follow the 6-cycle `A01–B01–C01–A10–B10–C10–A01`. When all weights are interior, `B01–C01–A10` already connects every line in those three classes (crossing `C01`, `A10`, and `B01` changes `z`, `x`, and `y` respectively), and the other three classes attach to it. One boundary weight removes two classes, leaving a connected four-class path; two opposite boundary weights leave a connected three-class path; three boundary weights cannot give three positive counts.

### Construction

Relabel the primes so that `p, q ≥ 3` and `r ≥ 2`, and start from `Mpq` and `Mpr`:

1. **Boundary strips.** Fusion gives `Mpq + Mpr → F(0,1,1) + Dp`. Since `F` is affine in each weight, `2 F(a,b,c) = F(a-1,b,c) + F(a+1,b,c)` (and likewise for `b` and `c`), so repeated midpoint steps from `F(0,1,1)` reach `F(0,1,c)` for `0 ≤ c ≤ r` and `F(0,b,1)` for `0 ≤ b ≤ q` (all positive molecules except the endpoints `Mpr` and `Mpq`).
2. **Interior seed.** Reacting `F(0,1,r-1) + F(0,q-1,1) → F(1,1,r-1) + F(1,q-1,1)` produces interior molecules; midpoint steps in `b` down from `q-1` reach `F(1,1,1)`.
3. **All positive profiles.** Midpoint walks along `a`, `b`, and `c` reach every profile with at least two interior weights. The remaining positive profiles have one interior weight and two opposite boundary weights; splitting one step inward along an adjacent interior weight (e.g. `2 F(a,1,r) → F(a,0,r) + F(a,2,r)`, using `b` if `a` is interior and `a` otherwise, valid since `p, q ≥ 3`) reaches them using only positive molecules.
4. **Missing binary and dimers.** `2 F(1,1,0) → Mqr + F(1,2,0)` produces `Mqr` (with `F(1,2,0)` positive since `p ≥ 2`, `q ≥ 3`). Fusing pairs of binaries sharing each element gives `Dp`, `Dq`, and `Dr`.

For any other feed pair, steps 1–2, the interior walk of step 3, and the `Mqr` step of step 4 only require the shared element to be `≥ 2`, the second coordinate `≥ 3`, and the third `≥ 2`. Putting the shared element first and an odd prime second therefore produces the missing binary even when the shared element is `2`, after which the odd-prime ordering above applies.

Finally, each use of an intermediate can be prepared on fresh feed copies (concatenating preparations and retaining byproducts), lifting production trees to finite ordered batches of `2→2` steps. Because the endpoint rule allows any geometric isomer with a produced formula, `C` itself appears in the final stock.

## Lean formalization

`GeneralSynthesis.every_molecule_with_elements` in [GeneralSynthesis.lean](lean/CyclicAtoms/GeneralSynthesis.lean) formalizes this entire theorem from the original `IsMolecule` definition in [Defs.lean](lean/CyclicAtoms/Defs.lean), and `GeneralSynthesis.valid_iff_original_molecule` proves the equivalence between the parity formula catalog `Valid` and existence of an original `IsMolecule` configuration. The proof uses only `[propext, Classical.choice, Quot.sound]` (no `native_decide`, custom axioms, or `sorry`). See [PROOF_AUDIT.md](lean/PROOF_AUDIT.md) for the module map.

## Explicit `{3, 5, 7}` certificates

For `{3, 5, 7}`, there are 86 molecular formulas (80 ternary, 3 binary, 3 dimer). [universal_synthesis.py](chemistry/universal_synthesis.py) generates explicit ordered `2→2` batches for all 258 `(feed pair, target)` combinations in [universal_synthesis.json](chemistry/output/universal_synthesis.json), independently checked in Lean by `Geometry.every_molecule_with_elements357` ([GeometricSynthesis.lean](lean/CyclicAtoms/GeometricSynthesis.lean)).

| Feed pair | Three-element targets | Full catalog | Max events in certificates |
|---|---:|---:|---:|
| M35, M37 | 80/80 | 86/86 | 46 |
| M35, M57 | 80/80 | 86/86 | 33 |
| M37, M57 | 80/80 | 86/86 | 22 |

## Why byproducts are necessary

A stock containing only `Mpq` and `Mqr` always satisfies `q nq = p np + r nr`, whereas the connected molecule `F(1,0,r) = (qr, (p-1)r, q)` violates this by `2qr` (for `{3, 5, 7}`, `MAX = (35,14,5)` has `5 n5 = 70 ≠ 140 = 3 n3 + 7 n7`).

## Reproduce

```sh
python -m chemistry.universal_synthesis
python -m verification.check_universal_synthesis
python -m chemistry.verify
cd lean && lake build
```
