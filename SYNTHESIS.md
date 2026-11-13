# Shortest syntheses of MAX3,5,7

`A = M35 = [5,3,0]`, `B = M37 = [7,0,3]`, `C = M57 = [0,7,5]`, `Dp = p_2`, and `MAX = [35,14,5]`, where `[a,b,c]` denotes `3_a 5_b 7_c`.

From unlimited feedstocks of the listed supplies (with closed byproducts allowed), we minimize total reaction events and distinct reaction types (counting reversible equations once, and parallel firings as separate events) under the `1→2`, `2→1`, and `2→2` model from [CLOSED_CHEMISTRY.md](CLOSED_CHEMISTRY.md). All witness routes use only `2→2` steps.

| Supply | Minimum events | Minimum types | Events in the type-minimal example |
|---|---:|---:|---:|
| A,B | 11 | 7 | 12 |
| A,C | 7 | 4 | 11 |
| B,C | 16 | 7 | 23 |
| A,B,C | 7 | 4 | 11 |

## Graphs and curved pictures of the A,C routes

Let `Xk = [5k,7+k,5]` (`X0 = M57`, `X7 = MAX`). Each step in the 7-event ladder adds `M35` and releases `D5`, replacing an upper 5-atom with a new row of five 3-atoms and two 5-atoms (read top row left-to-right, bottom row right-to-left).

| Route | Bond graphs | Human-style pictures |
|---|---|---|
| Seven events | [PNG](chemistry/output/synthesis_seven_graphs.png), [SVG](chemistry/output/synthesis_seven_graphs.svg) | [PNG](chemistry/output/synthesis_seven_human.png), [SVG](chemistry/output/synthesis_seven_human.svg) |
| Four types | [PNG](chemistry/output/synthesis_four_graphs.png), [SVG](chemistry/output/synthesis_four_graphs.svg) | [PNG](chemistry/output/synthesis_four_human.png), [SVG](chemistry/output/synthesis_four_human.svg) |

![Seven-event route as bond graphs](chemistry/output/synthesis_seven_graphs.png)

![Seven-event route in the curved style](chemistry/output/synthesis_seven_human.png)

The four-type diagrams fire each row 4, 4, 2, and 1 times, turning `8 M35 + 4 M57` into `MAX + X1 + 8 D5 + 2 M57`.

![Four reaction types as bond graphs](chemistry/output/synthesis_four_graphs.png)

![Four reaction types in the curved style](chemistry/output/synthesis_four_human.png)

In the curved pictures only marked contacts on the dotted circle are bonds; other crossings are visual only. Regenerate figures with `python -m chemistry.synthesis_plots` (data in [synthesis_picture_data.json](chemistry/output/synthesis_picture_data.json)).

## Optimality and executable batches

Event minima come from integer optimization (HiGHS, zero relative gap) over both directions of all 86-catalog channels, then scheduling each optimal multiset from zero intermediate stock. Type minima come from breadth-first search over synthesizable species: once a reaction fires, both sides are established and unlimited feedstocks can reproduce any established intermediate.

The objectives are independent (the 7-event `A,C` route uses 7 types; the 4-type witness uses 11 events). No supply can produce `MAX` without byproducts, since reversing such a route would contradict the obstruction in [CLOSED_CHEMISTRY.md](CLOSED_CHEMISTRY.md).

Tables below list reactions in execution order with firing counts.

## Supply A, B

### Event-minimal route

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

| Reaction | Firings |
|---|---:|
| `C + A → D5 + [5,8,5]` | 4 |
| `A + [5,8,5] → D5 + [10,9,5]` | 4 |
| `[10,9,5] + [10,9,5] → C + [20,11,5]` | 2 |
| `[20,11,5] + [20,11,5] → [5,8,5] + MAX` | 1 |

## Supply B, C

### Event-minimal route

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

Same optimal routes as Supply `A, C` (7 events; 4 types in 11 events).

## Reproduce

```sh
python -m chemistry.synthesis
python -m chemistry.verify
```

The search and batch expansion are in [synthesis.py](chemistry/synthesis.py), writing ordered sequences and reaction types to [synthesis.json](chemistry/output/synthesis.json).
