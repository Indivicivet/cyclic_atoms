# Proof sketches

Longer proof sketches for results stated in [THEORY.md](THEORY.md).

## Maximum size for four primes

For primes $s < p < q < r$, the maximum size of a molecule with element set $\{s, p, q, r\}$ is

$$
M(s,p,q,r) = pqr + (s-1)qr + (p-1)r + q.
$$

### Upper bound

Group the $spqr$ grid sites by their $(q,r)$ coordinates $(y,z) \in \mathbb{Z}_q \times \mathbb{Z}_r$ into $qr$ slices of size $s \times p$. In slice $(y,z)$, let $a_{y,z}$ be the number of absent s-lines among $p$ possible ones, $b_{y,z}$ the number of absent p-lines among $s$, $d_{y,z} = a_{y,z} + b_{y,z}$ the total number of absent $(s,p)$-lines, $Q_z$ the number of q-lines at $r$-coordinate $z$, $R_y$ the number of r-lines at $q$-coordinate $y$, and $e_{y,z}$ the number of empty sites. Counting incidences in slice $(y,z)$ gives

$$
s a_{y,z} + p b_{y,z} = Q_z + R_y + 2e_{y,z}.
$$

Because $s < p$ and $e_{y,z} \ge 0$, every slice satisfies $Q_z + R_y \le p d_{y,z}$. Every slice also satisfies $d_{y,z} \ge 1$. If $Q_z + R_y > 0$, then $p d_{y,z} \ge Q_z + R_y \ge 1$ forces $d_{y,z} \ge 1$. If $Q_z + R_y = 0$, no q-line or r-line meets slice $(y,z)$. Since s-lines and p-lines stay inside the slice and the connected molecule contains q- and r-atoms, the slice must be empty, giving $d_{y,z} = s + p \ge 1$.

Let $Q = \sum_{z \in \mathbb{Z}_r} Q_z \ge 1$ and $R = \sum_{y \in \mathbb{Z}_q} R_y \ge 1$ be the total numbers of q-atoms and r-atoms, and set $D_z = \sum_{y \in \mathbb{Z}_q} d_{y,z}$ and $D = \sum_{z \in \mathbb{Z}_r} D_z$. The molecule has size

$$
N = qr(s+p) - D + Q + R.
$$

In each column $z \in \mathbb{Z}_r$, summing $d_{y,z} \ge 1$ and $Q_z + R_y \le p d_{y,z}$ over $y \in \mathbb{Z}_q$ gives $D_z \ge q$ and $q Q_z + R \le p D_z$. Adding $(q-p)q \le (q-p)D_z$ yields

$$
q(Q_z + q - p) + R \le q D_z.
$$

There are two cases depending on how $R$ compares to $q$:

1. If $R \le q$, then $R \ge 1$ gives $q(Q_z + q - p) + 1 \le q D_z$, so $Q_z + q - p + 1 \le D_z$ for every $z$. Summing over all $r$ columns gives $Q + r(q - p + 1) \le D$, and adding $R \le q$ yields $Q + R + qr \le D + (p-1)r + q$.
2. If $R \ge q$, summing $q(Q_z + q - p) + R \le q D_z$ over all $r$ columns gives $q Q + r R + qr(q - p) \le q D$. Since $r \ge q$ and $R \ge q$, we have $(r - q)(R - q) \ge 0$, or $r R \ge q R + q(r - q)$. Substituting this lower bound for $r R$ and dividing by $q$ again yields $Q + R + qr \le D + (p-1)r + q$.

In both cases $Q + R - D \le (p-1)r + q - qr$, so

$$
N = qr(s+p) - D + Q + R \le qr(s+p-1) + (p-1)r + q = pqr + (s-1)qr + (p-1)r + q.
$$

### Construction

Place all $pqr$ s-lines; fill $s-1$ s-layers with p-lines, and in the last s-layer fill $p-1$ p-coordinate slices with q-lines and the last slice with r-lines. Every point in $\mathbb{Z}_s \times \mathbb{Z}_p \times \mathbb{Z}_q \times \mathbb{Z}_r$ belongs to one s-line and one larger line, so every grid point has two incidences. The bond graph is connected because the s-lines link the s-layers, the p-lines in the first $s-1$ layers link all p-coordinates, the q-lines in the last s-layer link all q-coordinates, and the r-lines in the final $(s,p)$-slice link all r-coordinates.

### Lean formalization

The slice bound (`four_prime_slice_bound`), single-column step (`four_prime_column_bound`), column aggregation (`validColumns_aggregate`), deficit bound (`four_prime_deficit_bound`), upper bound (`four_prime_upper_bound` and `four_prime_upper_bound_of_columns`), and two-incidence property of the layered construction (`four_prime_construction_twice`) are formalized in [`lean/CyclicAtoms/MaxSize.lean`](lean/CyclicAtoms/MaxSize.lean).
