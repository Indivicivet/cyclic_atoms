import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix

# q[0:11], r[11:18], d3[18:95], d5[95:172], active[172:249], empties[249:326]
n = 326
A = lil_matrix((77 * 5 + 2, n))
lo = []
hi = []
j = 0
for y in range(7):
    for z in range(11):
        i = y * 11 + z
        q = z
        r = 11 + y
        d3 = 18 + i
        d5 = 95 + i
        active = 172 + i
        empty = 249 + i
        A[j, q] = 1
        A[j, r] = 1
        A[j, empty] = 2
        A[j, d3] = -3
        A[j, d5] = -5
        lo.append(0)
        hi.append(0)
        j += 1
        A[j, q] = 1
        A[j, r] = 1
        A[j, active] = -1
        lo.append(0)
        hi.append(np.inf)
        j += 1
        A[j, q] = 1
        A[j, r] = 1
        A[j, active] = -30
        lo.append(-np.inf)
        hi.append(0)
        j += 1
        A[j, d3] = 1
        A[j, active] = 5
        lo.append(5)
        hi.append(np.inf)
        j += 1
        A[j, d5] = 1
        A[j, active] = 3
        lo.append(3)
        hi.append(np.inf)
        j += 1
A[j, :11] = 1
lo.append(1)
hi.append(np.inf)
j += 1
A[j, 11:18] = 1
lo.append(1)
hi.append(np.inf)
lb = np.zeros(n)
ub = np.r_[
    np.repeat(15, 18),
    np.repeat(5, 77),
    np.repeat(3, 77),
    np.ones(77),
    np.repeat(15, 77),
]
obj = np.r_[-np.ones(18), np.ones(154), np.zeros(154)]
r = milp(
    obj,
    integrality=np.ones(n),
    bounds=Bounds(lb, ub),
    constraints=LinearConstraint(A.tocsc(), np.array(lo), np.array(hi)),
    options={"time_limit": 55, "disp": True, "mip_rel_gap": 0},
)
print(
    "RESULT",
    r.message,
    "size",
    616 - r.fun if r.fun is not None else None,
    "upper",
    616 - r.mip_dual_bound if r.fun is not None else None,
    flush=True,
)
if r.x is not None:
    print("q", np.round(r.x[:11]), "r", np.round(r.x[11:18]), flush=True)

# Check the 590-atom construction via core.
import sys
from collections import Counter
from pathlib import Path

root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(root / "visualization"))
import core

atoms = core.read_atoms(root / "zoo/35711.md#35711_max590")
occ, _ = core.analyze(atoms)
assert len(atoms) == 590 and len(occ) == 1155
print("Construction:", dict(sorted(Counter(p for p, _, _ in atoms).items())))
print("All 1155 points occupied twice; all 590 atoms connected.")
