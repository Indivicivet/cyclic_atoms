# Shortest syntheses of MAX3,5,7

A = M35 = [5,3,0], B = M37 = [7,0,3], C = M57 = [0,7,5]. Every [a,b,c] denotes the molecule 3_a 5_b 7_c. Dp is a bonded p-dimer. MAX = [35,14,5].

The listed feedstocks are unlimited. No other molecules are initially available. The goal is at least one MAX, with arbitrary closed byproducts allowed. We use the balanced closed-endpoint model in [CLOSED_CHEMISTRY.md](CLOSED_CHEMISTRY.md), allowing 1→2, 2→1 and 2→2. All witness routes below actually use only 2→2. No continuous mechanism or low-cut realization is asserted.

A type specifies the actual molecular formulas, with a reversible equation counted once. Changing an intermediate's formula changes the type, even when the same growth pattern is used. Each occurrence of a reaction, including two occurrences run in parallel, counts as a separate event.

| Supply | Minimum events | Minimum types | Events in the type-minimal example |
|---|---:|---:|---:|
| A,B | 11 | 7 | 12 |
| A,C | 7 | 4 | 11 |
| B,C | 16 | 7 | 23 |
| A,B,C | 7 | 4 | 11 |

## Graphs and curved pictures of the A,C routes

Let `Xk = [5k,7+k,5]`, so X0 is M57 and X7 is MAX. Each seven-event arrow adds one M35 and releases one D5. Read its top row left to right, then its bottom row right to left. The graph drawings keep the seven CRT slices in fixed rows: each step replaces one of the upper 5-atoms with a new row containing five 3-atoms and two 5-atoms.

| Route | Bond graphs | Human-style pictures |
|---|---|---|
| Seven events | [PNG](chemistry/output/synthesis_seven_graphs.png), [SVG](chemistry/output/synthesis_seven_graphs.svg) | [PNG](chemistry/output/synthesis_seven_human.png), [SVG](chemistry/output/synthesis_seven_human.svg) |
| Four types | [PNG](chemistry/output/synthesis_four_graphs.png), [SVG](chemistry/output/synthesis_four_graphs.svg) | [PNG](chemistry/output/synthesis_four_human.png), [SVG](chemistry/output/synthesis_four_human.svg) |

![Seven-event route as bond graphs](chemistry/output/synthesis_seven_graphs.png)

![Seven-event route in the curved style](chemistry/output/synthesis_seven_human.png)

The four-type diagrams show one elementary equation per row, fired 4, 4, 2 and 1 times respectively. Both copies of the reactant appear in the last two rows. This grouped batch starts with 8 M35 and 4 M57, and ends with MAX, X1, eight D5 and two returned M57. It illustrates the four types without optimizing initial feed quantities.

![Four reaction types as bond graphs](chemistry/output/synthesis_four_graphs.png)

![Four reaction types in the curved style](chemistry/output/synthesis_four_human.png)

Each graph vertex or curved line is one atom; element colours are consistent throughout. In the curved pictures only marked contacts on the dotted circle are bonds. Other curve crossings have no bonding meaning. These are closed endpoint structures, not internal bond-breaking trajectories. All displayed molecules and equations are checked exactly before rendering.

Run `python -m chemistry.synthesis_plots` to regenerate the four PNG/SVG figures. The exact molecule phases and batch inventory are in [synthesis_picture_data.json](chemistry/output/synthesis_picture_data.json).

## Optimality and executable batches

For event count, integer optimization minimizes total firings subject to nonnegative final inventory of every non-feedstock and at least one MAX. Ignoring ordering makes this a lower bound. Each optimal firing multiset was then scheduled and replayed from zero intermediate stock, attaining that lower bound. Thus an unseeded catalytic cycle cannot invalidate the claimed minimum. The model includes both directions of every channel in the complete 86-formula catalog. HiGHS reported optimality with zero relative gap. These are computational results, not Lean formalizations.

For type count, exhaustive breadth-first search tracks the set of synthesizable species. A reaction can establish its outputs when all its inputs are established. Unlimited feed allows any established intermediate to be remade in any finite quantity, including two copies of one reactant. Once a type has fired, all species on both sides are established; repeating it cannot add another species. Search depth therefore counts new types exactly. The first depth reaching MAX is the minimum. Recursive expansion and inventory replay give finite batches without borrowed intermediates.

The objectives are independent. The last table column describes an explicit type-minimal witness, not the minimum event count among all type-minimal witnesses. In particular, the seven-event A,C ladder uses seven types; the four-type A,C recipe shown here uses eleven events.

If the final inventory must contain only MAX molecules and no other products, none of these feed supplies can do that using these small closed steps: reversing such a finite route would escape from a collection of only maxima, contradicting the earlier obstruction.

## Supply A, B

### Event-minimal route

Execute the rows in order, with the indicated number of firings.

| Reaction | Firings |
|---|---:|
| `A + B → D3 + [10,3,3]` | 3 |
| `A + [10,3,3] → D3 + [13,6,3]` | 2 |
| `B + [10,3,3] → D3 + [15,3,6]` | 1 |
| `[13,6,3] + [15,3,6] → D5 + [28,7,9]` | 1 |
| `A + [13,6,3] → D3 + [16,9,3]` | 1 |
| `A + [16,9,3] → D3 + [19,12,3]` | 1 |
| `A + [19,12,3] → D3 + [22,15,3]` | 1 |
| `[22,15,3] + [28,7,9] → [15,8,7] + MAX` | 1 |

### Type-minimal route

Execute the rows in order, with the indicated number of firings.

| Reaction | Firings |
|---|---:|
| `A + B → D3 + [10,3,3]` | 4 |
| `A + [10,3,3] → D3 + [13,6,3]` | 3 |
| `A + [13,6,3] → D3 + [16,9,3]` | 1 |
| `[13,6,3] + [16,9,3] → B + [22,15,3]` | 1 |
| `B + [10,3,3] → D3 + [15,3,6]` | 1 |
| `[13,6,3] + [15,3,6] → D5 + [28,7,9]` | 1 |
| `[22,15,3] + [28,7,9] → [15,8,7] + MAX` | 1 |

## Supply A, C

### Event-minimal route

Execute the rows in order, with the indicated number of firings.

| Reaction | Firings |
|---|---:|
| `C + A → D5 + [5,8,5]` | 1 |
| `A + [5,8,5] → D5 + [10,9,5]` | 1 |
| `A + [10,9,5] → D5 + [15,10,5]` | 1 |
| `A + [15,10,5] → D5 + [20,11,5]` | 1 |
| `A + [20,11,5] → D5 + [25,12,5]` | 1 |
| `A + [25,12,5] → D5 + [30,13,5]` | 1 |
| `A + [30,13,5] → D5 + MAX` | 1 |

### Type-minimal route

Execute the rows in order, with the indicated number of firings.

| Reaction | Firings |
|---|---:|
| `C + A → D5 + [5,8,5]` | 4 |
| `A + [5,8,5] → D5 + [10,9,5]` | 4 |
| `[10,9,5] + [10,9,5] → C + [20,11,5]` | 2 |
| `[20,11,5] + [20,11,5] → [5,8,5] + MAX` | 1 |

## Supply B, C

### Event-minimal route

Execute the rows in order, with the indicated number of firings.

| Reaction | Firings |
|---|---:|
| `C + B → D7 + [7,7,6]` | 3 |
| `C + [7,7,6] → D7 + [7,14,9]` | 1 |
| `B + [7,7,6] → D7 + [14,7,7]` | 2 |
| `B + [14,7,7] → D7 + [21,7,8]` | 2 |
| `B + [21,7,8] → D7 + [28,7,9]` | 2 |
| `B + [28,7,9] → D7 + [35,7,10]` | 2 |
| `[7,14,9] + [35,7,10] → [17,12,9] + [25,9,10]` | 1 |
| `B + [17,12,9] → A + [19,9,12]` | 1 |
| `[25,9,10] + [35,7,10] → [30,3,15] + [30,13,5]` | 1 |
| `A + [30,13,5] → D5 + MAX` | 1 |

### Type-minimal route

Execute the rows in order, with the indicated number of firings.

| Reaction | Firings |
|---|---:|
| `C + B → D7 + [7,7,6]` | 8 |
| `B + [7,7,6] → D7 + [14,7,7]` | 6 |
| `[14,7,7] + [14,7,7] → C + [28,7,9]` | 3 |
| `C + [7,7,6] → D7 + [7,14,9]` | 2 |
| `[7,14,9] + [28,7,9] → [15,18,9] + [20,3,9]` | 2 |
| `[15,18,9] + [15,18,9] → [5,18,15] + [25,18,3]` | 1 |
| `[25,18,3] + [28,7,9] → [18,11,7] + MAX` | 1 |

## Supply A, B, C

### Event-minimal route

Execute the rows in order, with the indicated number of firings.

| Reaction | Firings |
|---|---:|
| `C + A → D5 + [5,8,5]` | 1 |
| `A + [5,8,5] → D5 + [10,9,5]` | 1 |
| `A + [10,9,5] → D5 + [15,10,5]` | 1 |
| `A + [15,10,5] → D5 + [20,11,5]` | 1 |
| `A + [20,11,5] → D5 + [25,12,5]` | 1 |
| `A + [25,12,5] → D5 + [30,13,5]` | 1 |
| `A + [30,13,5] → D5 + MAX` | 1 |

### Type-minimal route

Execute the rows in order, with the indicated number of firings.

| Reaction | Firings |
|---|---:|
| `C + A → D5 + [5,8,5]` | 4 |
| `A + [5,8,5] → D5 + [10,9,5]` | 4 |
| `[10,9,5] + [10,9,5] → C + [20,11,5]` | 2 |
| `[20,11,5] + [20,11,5] → [5,8,5] + MAX` | 1 |

## Reproduce

```sh
python -m chemistry.synthesis
python -m chemistry.verify
```

The search and batch expansion are in [synthesis.py](chemistry/synthesis.py). Exact ordered sequences and all intermediate-producing reaction types are saved in [synthesis.json](chemistry/output/synthesis.json).
