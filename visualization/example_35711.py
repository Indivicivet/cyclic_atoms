"""Generate the circle and layer views for the 590-atom 3,5,7,11 example."""

from pathlib import Path
import argparse
import matplotlib.pyplot as plt
from matplotlib.patches import Patch
from core import read_atoms, describe, circle

root = Path(__file__).resolve().parents[1]
p = argparse.ArgumentParser()
p.add_argument("--outdir", default=".")
a = p.parse_args()
out = Path(a.outdir)
out.mkdir(parents=True, exist_ok=True)
atoms = read_atoms(root / "zoo/35711_max590.md")
describe(atoms)
circle(atoms, out / "35711_max590_circle.png", "3–5–7–11: 590 atoms")
fig, axes = plt.subplots(1, 3, figsize=(13, 5), sharey=True)
for u, ax in enumerate(axes):
    for x in range(5):
        for y in range(7):
            col = "#e49327" if u < 2 else ("#168d84" if x < 4 else "#cb5964")
            ax.add_patch(
                plt.Rectangle((x, y), 1, 1, facecolor=col, edgecolor="white", lw=1)
            )
    ax.set_xlim(0, 5)
    ax.set_ylim(0, 7)
    ax.set_aspect("equal")
    ax.set_xticks([i + 0.5 for i in range(5)], labels=range(5))
    ax.set_yticks([i + 0.5 for i in range(7)], labels=range(7))
    ax.set_xlabel("5-coordinate x")
    ax.set_title(f"3-layer u = {u}")
axes[0].set_ylabel("7-coordinate y")
fig.legend(
    handles=[
        Patch(color="#e49327", label="5-atom"),
        Patch(color="#168d84", label="7-atom"),
        Patch(color="#cb5964", label="11-atom"),
    ],
    loc="lower center",
    ncol=3,
)
fig.suptitle(
    "590 atoms: each (x,y,z) has one 3-atom joining all three layers\nEach coloured square represents all 11 z-coordinates; see README for line directions"
)
fig.tight_layout(rect=(0, 0.07, 1, 0.9))
fig.savefig(out / "35711_max590_layers.png", dpi=180)
plt.close(fig)
