# Visualisation

From the project root, install dependencies with `python -m pip install -r requirements.txt`, then run:

```sh
python visualization/circle.py zoo/235.md#2_3_5_max
python visualization/graph.py zoo/235.md#2_3_5_max
python visualization/example_3711.py
python visualization/example_35711.py
python visualization/wip_3d.py
```

For the 2D scripts, omit the output path (or `--outdir`) to open interactive plot windows directly, or pass an output file / `--outdir output` to save PNGs:

```sh
python visualization/circle.py zoo/235.md#2_3_5_max output/circle.png
python visualization/graph.py zoo/235.md#2_3_5_max output/graph.png
python visualization/example_3711.py --outdir output
python visualization/example_35711.py --outdir output
```

Both general renderers accept `path.md#section` (or `path.md` when the file has a single fenced block), as well as rational 0A JSON and signed 0B JSON. They check exact bond occupancy, connectivity and, for 0B, opposite colours. The circular view shows one ring per atom and one dot per point, with a highlighted atom and its bonds; use `--highlight INDEX` to select a different input-list index. Dots with the same angle are bonded. Spokes are schematic; crossings do not form bonds. Large examples are best viewed zoomed in.

The graph shows atoms as vertices, with element encoded by colour and shape. Vertex numbers are input indices. Crossings do not create bonds. Parallel bonds may overlap visually; multiplicity remains in the data. To keep the graph readable, it rejects molecules over 150 atoms; use the structured layer view for larger examples.

The 3D viewer has a molecule picker and controls for ring radius and z spacing. Atoms are dots with circular loops that meet at bond junctions. Radius zero gives a point-and-line graph; z spacing zero makes the drawing flat. Drag to rotate and scroll to zoom. Coordinates are schematic.

The 3–7–11 map has a dot per 3-atom. Each row is an 11-atom; each pair of column lines represents two 7-atoms.

The 590-atom map displays three $5 \times 7$ slices, each square representing all 11 values of $z$. Each 3-atom joins corresponding $(x,y,z)$ in all three layers. In layers 0 and 1, 5-atoms run along $x$ at fixed $(y,z)$. In layer 2, 7-atoms run along $y$ at fixed $(x,z)$ for $x=0,\ldots,3$; 11-atoms run along $z$ at fixed $(x=4,y)$. Colours indicate element, not individual atom identity.

## Molecule zoo explorer

From the project root:

```sh
python -m pip install -r requirements.txt
python visualization/zoo_explorer.py
```

The explorer discovers exact 0A/0B blocks in `zoo/`, checks their bonds and
connectivity, and sorts molecules by atom count. Each list entry shows its formula
and a thumbnail whose coloured segments show the element counts. Filter by name
or formula, click a molecule, or use Previous / Next (`Alt+Left` / `Alt+Right`).

Tabs show the in/out curves from `humanity/visualiser.py`, radial curves from
`humanity/cp_pair_diagrams.py`, concentric rings, the bond graph, and the existing
structured maps for `3711_max` and `35711_max590`. The graph retains its 150-atom
limit. In/out curves require a bipartite graph; signed 0B assignments are preserved,
while assignments for unsigned 0A molecules are inferred. Use the concentric
view's atom index to highlight its bonds. The plot toolbar provides zoom, pan,
reset and image export.

All drawings and thumbnails are generated at runtime. Only the selected view is
rendered, and switching views replaces the previous figure. No prebuilt images
or disk cache are required. Curve colours match the element colours in the other
views. The drawings are schematic, not physical geometry.

To browse a different folder or a selection of Markdown / JSON files:

```sh
python visualization/zoo_explorer.py --zoo path/to/examples
python visualization/zoo_explorer.py "zoo/235.md#2_3_5_max" zoo/small.md
```

To add a general representation, add a drawing function and a `Representation`
entry to `REPRESENTATIONS`. The function receives the figure, molecule and
highlighted atom index. The two fixed structured maps are keyed by their exact
zoo source, so a different molecule with the same formula cannot receive a map
that does not describe it.

Headless checks:

```sh
python verification/verify_zoo_explorer.py
```
