"""Generate the circle and row-column connectivity views for 3,7,11."""
from pathlib import Path
import argparse
import matplotlib.pyplot as plt
from core import read_atoms,describe,circle
root=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser(); p.add_argument('--outdir',default='.'); a=p.parse_args()
out=Path(a.outdir); out.mkdir(parents=True,exist_ok=True)
atoms=read_atoms(root/'zoo/3711_max.json'); describe(atoms)
circle(atoms,out/'3711_circle.png','3–7–11: 106 atoms')
fig,ax=plt.subplots(figsize=(12,8))
for y in range(11):
    ax.plot([-.15,6.15],[y,y],color='#cb5964',lw=2); ax.text(6.25,y,'11',color='#cb5964',va='center')
for x in range(7):
    for d in (-.08,.08): ax.plot([x+d,x+d],[-.2,10.2],color='#168d84',lw=1.5)
    ax.text(x,10.45,'7 + 7',color='#168d84',ha='center')
for x in range(7):
    for y in range(11): ax.scatter(x,y,c='#8159af',s=34,zorder=3)
ax.set_xlim(-.5,7);ax.set_ylim(-.5,11);ax.set_aspect('equal');ax.axis('off')
ax.set_title('3–7–11: each dot is a 3-atom; row/column lines are its partners')
fig.tight_layout(); fig.savefig(out/'3711_structure.png',dpi=180); plt.close(fig)
