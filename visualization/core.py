"""Exact 0A/0B parsing, molecule validation and plotting helpers."""

import ast
import json
import re
from collections import Counter, defaultdict
from fractions import Fraction
from math import cos, pi, prod, sin
from pathlib import Path

import matplotlib.pyplot as plt
import networkx as nx
from matplotlib.lines import Line2D

COLORS = {
    2: "#2878b5",
    3: "#8159af",
    4: "#159f85",
    5: "#e49327",
    7: "#168d84",
    11: "#cb5964",
}
SHAPES = {2: "o", 3: "^", 4: "D", 5: "s", 7: "P", 11: "h"}


def read_atoms(target):
    raw_path, _, section = str(target).partition("#")
    path = Path(raw_path)
    text = path.read_text()
    if path.suffix == ".md":
        blocks = [
            (
                headings[-1].strip() if headings else "",
                m.group(1),
                m.group(2),
            )
            for m in re.finditer(r"```(0A|0B)\s*\n(.*?)\n```", text, re.DOTALL)
            for headings in [re.findall(r"(?:^|\n)#+\s*([^\n]+)", text[: m.start()])]
        ]
        if not blocks:
            raise ValueError("expected a fenced 0A or 0B block")
        if section:
            matches = [(n, b) for h, n, b in blocks if h == section]
            if not matches:
                available = ", ".join(f"#{h}" for h, _, _ in blocks if h)
                raise ValueError(
                    f"section #{section} not found in {path} (available: {available})"
                )
            notation, body = matches[0]
        elif len(blocks) == 1:
            _, notation, body = blocks[0]
        else:
            available = ", ".join(f"#{h}" for h, _, _ in blocks if h)
            raise ValueError(
                f"multiple sections in {path}; specify one of: {available}"
            )
        if notation == "0A":
            pattern = r"(?:\(\s*(\d+)\s*,\s*([+-]?\d+(?:/\d+)?)\s*\)|\[\s*(\d+)\s*,\s*([+-]?\d+(?:/\d+)?)\s*\])"
            entries = [
                (p1 or p2, a1 or a2) for p1, a1, p2, a2 in re.findall(pattern, body)
            ]
            if not entries or re.sub(pattern, "", body).replace(",", "").strip():
                raise ValueError("invalid 0A notation")
            data = entries
        else:
            data = ast.literal_eval("{" + body + "}")
    else:
        data = json.loads(text)
    if isinstance(data, list):
        return [(int(p), Fraction(a) % Fraction(1, int(p)), None) for p, a in data]
    grid_size = prod(int(p) for p in data)
    atoms = []
    for key, groups in data.items():
        p = int(key)
        if len(groups) != 2:
            raise ValueError("0B needs [outward, inward]")
        for color, inds in enumerate(groups):
            for i in inds:
                if not isinstance(i, int) or not 0 <= i < grid_size:
                    raise ValueError("index outside grid")
                atoms.append((p, Fraction(i, grid_size) % Fraction(1, p), color))
    return atoms


def sites(atom):
    p, a, _ = atom
    if p < 2:
        raise ValueError("element must be at least 2")
    return [(a + Fraction(k, p)) % 1 for k in range(p)]


def analyze(atoms):
    occ = defaultdict(list)
    for i, atom in enumerate(atoms):
        for x in sites(atom):
            occ[x].append(i)
    bad = {x: v for x, v in occ.items() if len(v) != 2}
    if bad:
        raise ValueError(
            f"{len(bad)} positions have occupancy other than 2; first: {next(iter(bad.items()))}"
        )
    G = nx.MultiGraph()
    G.add_nodes_from(range(len(atoms)))
    for x, (i, j) in occ.items():
        if i == j:
            raise ValueError("self bond")
        G.add_edge(i, j, phase=x)
        if (
            atoms[i][2] is not None
            and atoms[j][2] is not None
            and atoms[i][2] == atoms[j][2]
        ):
            raise ValueError(f"0B has same-colour bond at {x}")
    if not atoms or not nx.is_connected(G):
        raise ValueError("configuration is not a connected molecule")
    return occ, G


def describe(atoms):
    occ, graph = analyze(atoms)
    print(
        "Atoms:",
        len(atoms),
        "formula:",
        dict(sorted(Counter(a[0] for a in atoms).items())),
        "bonds:",
        len(occ),
        "bipartite:",
        nx.is_bipartite(graph),
    )


def finish_figure(fig, output=None, dpi=180):
    if output is None:
        plt.show()
    else:
        Path(output).parent.mkdir(parents=True, exist_ok=True)
        fig.savefig(output, dpi=dpi)
        plt.close(fig)


def circle(atoms, output=None, title=None, highlight=0, dpi=180):
    occ, G = analyze(atoms)
    n = len(atoms)
    fig, ax = plt.subplots(figsize=(11, 11), subplot_kw={"aspect": "equal"})
    radii = [0.13 + 0.79 * (i / max(1, n - 1)) for i in range(n)]
    for i, atom in enumerate(atoms):
        rad = radii[i]
        col = COLORS.get(atom[0], "#666666")
        ax.add_patch(
            plt.Circle(
                (0, 0),
                rad,
                fill=False,
                lw=0.28 if n > 80 else 0.8,
                color=col,
                alpha=0.55,
            )
        )
        angles = [2 * pi * float(x) for x in sites(atom)]
        ax.scatter(
            [rad * sin(t) for t in angles],
            [rad * cos(t) for t in angles],
            s=1.4 if n > 80 else 20,
            c=col,
            zorder=3,
        )
    if highlight is not None:
        i = highlight
        if not 0 <= i < n:
            raise ValueError("highlight index out of range")
        ax.add_patch(
            plt.Circle((0, 0), radii[i], fill=False, color="#e4b10c", lw=1.9, zorder=4)
        )
        for x in sites(atoms[i]):
            j = next(v for v in occ[x] if v != i)
            t = 2 * pi * float(x)
            ax.plot(
                [radii[i] * sin(t), radii[j] * sin(t)],
                [radii[i] * cos(t), radii[j] * cos(t)],
                color="#e4b10c",
                lw=1.2,
                zorder=5,
            )
    elements = sorted({a[0] for a in atoms})
    ax.legend(
        handles=[
            Line2D(
                [0],
                [0],
                marker="o",
                lw=0,
                color=COLORS.get(p, "#666"),
                label=f"{p}-atoms",
            )
            for p in elements
        ],
        loc="lower left",
    )
    ax.set_title(title or f"{n} atoms — concentric view")
    ax.set_xlim(-1.05, 1.05)
    ax.set_ylim(-1.05, 1.05)
    ax.axis("off")
    fig.tight_layout()
    finish_figure(fig, output, dpi)


def graph(atoms, output=None, title=None, dpi=180):
    occ, G = analyze(atoms)
    if len(atoms) > 150:
        raise ValueError(
            "Graph is too large for this overview; use a structured map or concentric view"
        )
    pos = nx.spring_layout(G, seed=12, iterations=250)
    fig, ax = plt.subplots(figsize=(12, 9))
    nx.draw_networkx_edges(G, pos, ax=ax, width=0.8, alpha=0.45)
    for p in sorted({a[0] for a in atoms}):
        nodes = [i for i, a in enumerate(atoms) if a[0] == p]
        nx.draw_networkx_nodes(
            G,
            pos,
            nodelist=nodes,
            node_color=COLORS.get(p, "#666"),
            node_shape=SHAPES.get(p, "o"),
            node_size=240 if len(atoms) > 40 else 650,
            ax=ax,
            label=f"{p}-atoms",
        )
    nx.draw_networkx_labels(
        G,
        pos,
        labels={i: str(i) for i in G},
        font_size=5 if len(atoms) > 40 else 8,
        font_color="white",
        ax=ax,
    )
    ax.legend()
    ax.axis("off")
    ax.set_title(title or f"{len(atoms)} atoms — bond graph; labels are 0A indices")
    fig.tight_layout()
    finish_figure(fig, output, dpi)
