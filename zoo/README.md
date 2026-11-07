# Zoo

Examples are grouped by prime family in [small.md](small.md), [235.md](235.md),
[3711.md](3711.md), and [35711.md](35711.md). Each `##` section contains a
fenced block of exact atom notation, as defined in [INTRO.md](../INTRO.md). 0A
entries are `(element, phase in turns)`; repeated entries are distinct atoms.
The signed example uses 0B and retains its outward and inward assignments. All
examples have been checked for exact double occupancy and connectivity.

| Section | Formula | Notes |
|---|---|---|
| [small.md#identical_twos](small.md#identical_twos) | `2_2` | Two parallel bonds |
| [small.md#composite_224](small.md#composite_224) | `2_2 4_1` | Composite element |
| [small.md#two_and_five](small.md#two_and_five) | `2_5 5_2` | Two-prime construction |
| [235.md#235_ten](235.md#235_ten) | `2_6 3_2 5_2` | Ten-atom structure |
| [235.md#235_branches](235.md#235_branches) | `2_10 3_10 5_2` | Five copies of the four-atom 3-2-2-3 branch |
| [235.md#2_3_5_max](235.md#2_3_5_max) | `2_15 3_5 5_3` | 23-atom maximum |
| [3711.md#3711_max](3711.md#3711_max) | `3_77 7_22 11_7` | 106-atom maximum |
| [35711.md#example_0b](35711.md#example_0b) | `3_14 5_8 7_5 11_3` | Signed example from INTRO.md, 30 atoms |
| [35711.md#35711_product](35711.md#35711_product) | `3_385 5_77 7_55 11_35` | Product, 552 atoms |
| [35711.md#35711_mixed588](35711.md#35711_mixed588) | `3_385 5_143 7_55 11_5` | Mixed, 588 atoms |
| [35711.md#35711_max590](35711.md#35711_max590) | `3_385 5_154 7_44 11_7` | Computed maximum, 590 atoms |

The larger examples use coordinate lines on a product of cyclic groups, mapped
to phases by the Chinese remainder theorem. The 3-5-7-11 examples fill the
three 3-coordinate layers with lines in the following directions:

- Product: 5, 7, then 11.
- Mixed 588: 5, 7, then 5 except for one 7-coordinate slice filled by 11.
- Maximum 590: 5, 5, then 7 except for one 5-coordinate slice filled by 11.

These files record a particular rotation and ordering; phases and labels may
differ from earlier pictures.
