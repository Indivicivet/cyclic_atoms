# Zoo

Run `python zoo/build_examples.py` from the project root to regenerate the 0A JSON data. Rational phases are exact strings. `example_0b.json` is the signed example from INTRO.md. All files have been checked for exact double occupancy and connectivity.

| File | Formula | Notes |
|---|---|---|
| `identical_twos.json` | `2_2` | Two parallel bonds |
| `composite_224.json` | `2_2 4_1` | Composite element |
| `two_and_five.json` | `2_5 5_2` | Two-prime construction |
| `235_ten.json` | `2_6 3_2 5_2` | Ten-atom structure |
| `235_branches.json` | `2_10 3_10 5_2` | Five branches |
| `23_max.json` | `2_15 3_5 5_3` | 23-atom maximum |
| `3711_max.json` | `3_77 7_22 11_7` | 106-atom maximum |
| `35711_product.json` | `3_385 5_77 7_55 11_35` | Product, 552 atoms |
| `35711_mixed588.json` | `3_385 5_143 7_55 11_5` | Mixed, 588 atoms |
| `35711_max590.json` | `3_385 5_154 7_44 11_7` | Computed maximum, 590 atoms |
| `example_0b.json` | `3_14 5_8 7_5 11_3` | Signed example, 30 atoms |

The generator chooses a particular rotation and CRT ordering; phases and labels may differ from earlier pictures.
