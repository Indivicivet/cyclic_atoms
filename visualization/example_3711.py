"""Generate the circle and row-column connectivity views for 3,7,11."""

import argparse
from pathlib import Path

import matplotlib.pyplot as plt

import core

root = Path(__file__).resolve().parents[1]
p = argparse.ArgumentParser()
p.add_argument("--outdir", default=None)
a = p.parse_args()
out = Path(a.outdir) if a.outdir else None
atoms = core.read_atoms(root / "zoo/3711.md#3711_max")
core.describe(atoms)
core.circle(atoms, out / "3711_circle.png" if out else None, "3–7–11: 106 atoms")
fig, ax = plt.subplots(figsize=(12, 8))
for y in range(11):
    ax.plot([-0.15, 6.15], [y, y], color="#cb5964", lw=2)
    ax.text(6.25, y, "11", color="#cb5964", va="center")
for x in range(7):
    for d in (-0.08, 0.08):
        ax.plot([x + d, x + d], [-0.2, 10.2], color="#168d84", lw=1.5)
    ax.text(x, 10.45, "7 + 7", color="#168d84", ha="center")
ax.scatter(
    [x for x in range(7) for y in range(11)],
    [y for x in range(7) for y in range(11)],
    c=core.COLORS[3],
    s=34,
    zorder=3,
)
ax.set_xlim(-0.5, 7)
ax.set_ylim(-0.5, 11)
ax.set_aspect("equal")
ax.axis("off")
ax.set_title("3–7–11: each dot is a 3-atom; row/column lines are its partners")
fig.tight_layout()
core.finish_figure(fig, out / "3711_structure.png" if out else None)
