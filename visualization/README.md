# Visualisation

From the project root, install dependencies with `python -m pip install -r requirements.txt`, then run:

```sh
python visualization/circle.py zoo/23_max.md circle.png
python visualization/graph.py zoo/23_max.md graph.png
python visualization/example_3711.py --outdir output
python visualization/example_35711.py --outdir output
```

Both general renderers accept the zoo's Markdown 0A and signed 0B blocks, as well as rational 0A JSON and signed 0B JSON. They check exact bond occupancy, connectivity and, for 0B, opposite colours. The circular view shows one ring per atom and one dot per point, with a highlighted atom and its bonds; use `--highlight INDEX` to select a different input-list index. Dots with the same angle are bonded. Spokes are schematic; crossings do not form bonds. Large examples are best viewed zoomed in.

The graph shows atoms as vertices, with element encoded by colour and shape. Vertex numbers are input indices. Crossings do not create bonds. Parallel bonds may overlap visually; multiplicity remains in the data. To keep the graph readable, it rejects molecules over 150 atoms; use the structured layer view for larger examples.

The 3–7–11 map has a dot per 3-atom. Each row is an 11-atom; each pair of column lines represents two 7-atoms.

The 590-atom map displays three $5 \times 7$ slices, each square representing all 11 values of $z$. Each 3-atom joins corresponding $(x,y,z)$ in all three layers. In layers 0 and 1, 5-atoms run along $x$ at fixed $(y,z)$. In layer 2, 7-atoms run along $y$ at fixed $(x,z)$ for $x=0,\ldots,3$; 11-atoms run along $z$ at fixed $(x=4,y)$. Colours indicate element, not individual atom identity.

Original images from the conversation are in `images/`. Their original plotting source was not available; these are new reproducible scripts for the same types of visualisation.
