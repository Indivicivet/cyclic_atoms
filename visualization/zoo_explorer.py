"""Browse exact zoo molecules and render their representations on demand.

Run from any directory with Python, for example:
    python visualization/zoo_explorer.py
    python visualization/zoo_explorer.py zoo/235.md#2_3_5_max

Add a representation to REPRESENTATIONS to expose another drawing function.
Figures and composition thumbnails are generated in memory, never loaded from PNGs.
"""

import argparse
import re
import sys
from collections import Counter
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path

import matplotlib as mpl
import networkx as nx
from PySide6.QtCore import QSize, Qt, QTimer
from PySide6.QtGui import QColor, QIcon, QKeySequence, QPainter, QPalette, QPixmap
from PySide6.QtWidgets import (
    QApplication,
    QHBoxLayout,
    QLabel,
    QLineEdit,
    QListWidget,
    QListWidgetItem,
    QMainWindow,
    QMessageBox,
    QPushButton,
    QSpinBox,
    QSplitter,
    QTabBar,
    QVBoxLayout,
    QWidget,
)

# isort: split
# Select PySide6 before importing the Matplotlib Qt backend.
from matplotlib.backends.backend_qtagg import FigureCanvasQTAgg, NavigationToolbar2QT
from matplotlib.figure import Figure
from matplotlib.lines import Line2D

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import humanity.cp_pair_diagrams as cp_pair_diagrams
import humanity.system as system
import humanity.visualiser as visualiser
import visualization.core as core
import visualization.example_3711 as example_3711
import visualization.example_35711 as example_35711


def catalogue(path):
    """Find exact-notation blocks, retaining the section names used by core."""
    if path.is_dir():
        return [
            target
            for child in sorted(path.rglob("*.md"))
            for target in catalogue(child)
        ]
    if path.suffix.lower() != ".md":
        return [str(path)]
    text = path.read_text(encoding="utf-8")
    targets = []
    for block in re.finditer(r"```(?:0A|0B)\s*\n.*?\n```", text, re.DOTALL):
        headings = re.findall(r"(?:^|\n)#+\s*([^\n]+)", text[: block.start()])
        targets.append(f"{path}#{headings[-1].strip()}" if headings else str(path))
    return list(dict.fromkeys(targets))


@dataclass
class Molecule:
    target: str
    atoms: list
    graph: nx.MultiGraph
    counts: dict
    sides: list | None

    @classmethod
    def load(cls, target):
        raw_path, _, section = str(target).partition("#")
        target = str(Path(raw_path).resolve()) + (f"#{section}" if section else "")
        atoms = core.read_atoms(target)
        _, graph = core.analyze(atoms)
        # Preserve signed 0B assignments. For unsigned 0A, choose one of the two
        # bipartite colourings; a non-bipartite molecule has no in/out drawing.
        if all(atom[2] is not None for atom in atoms):
            sides = [atom[2] for atom in atoms]
        elif nx.is_bipartite(graph):
            colouring = nx.bipartite.color(graph)
            sides = [colouring[i] for i in range(len(atoms))]
        else:
            sides = None
        return cls(
            str(target),
            atoms,
            graph,
            dict(sorted(Counter(atom[0] for atom in atoms).items())),
            sides,
        )

    @property
    def name(self):
        path, _, section = self.target.partition("#")
        return section or Path(path).stem

    @property
    def formula(self):
        return "  ".join(f"{p}_{count}" for p, count in self.counts.items())


def composition_icon(molecule, palette):
    """A count donut: each coloured segment is an element's share of atoms."""
    pixmap = QPixmap(112, 112)
    pixmap.fill(Qt.GlobalColor.transparent)
    painter = QPainter(pixmap)
    painter.setRenderHint(QPainter.RenderHint.Antialiasing)
    painter.setPen(Qt.PenStyle.NoPen)
    start = 90 * 16
    for p, count in molecule.counts.items():
        span = round(360 * 16 * count / len(molecule.atoms))
        painter.setBrush(QColor(core.COLORS.get(p, "#666666")))
        painter.drawPie(5, 5, 102, 102, start, -span)
        start -= span
    painter.setBrush(palette.brush(QPalette.ColorRole.Base))
    painter.drawEllipse(22, 22, 68, 68)
    painter.setPen(palette.color(QPalette.ColorRole.Text))
    font = painter.font()
    font.setPixelSize(29)
    font.setBold(True)
    painter.setFont(font)
    painter.drawText(
        pixmap.rect(), Qt.AlignmentFlag.AlignCenter, str(len(molecule.atoms))
    )
    painter.end()
    pixmap.setDevicePixelRatio(2)
    return QIcon(pixmap)


def curve_legend(ax, molecule):
    ax.legend(
        handles=[
            Line2D(
                [0], [0], color=core.COLORS.get(p, "#666666"), label=f"{p}-atoms × {n}"
            )
            for p, n in molecule.counts.items()
        ],
        loc="lower left",
    )
    ax.set_aspect("equal")
    ax.axis("off")


def draw_in_out(fig, molecule, highlight):
    if molecule.sides is None:
        raise ValueError(
            "This bond graph is not bipartite, so no in/out assignment exists."
        )
    groups = [[i for i, side in enumerate(molecule.sides) if side == s] for s in (0, 1)]
    generator = visualiser.CurveGenerator(
        n_up_atoms=len(groups[0]), n_down_atoms=len(groups[1]), n_thetas=4096
    )
    ax = fig.add_subplot()
    # Generate one curve at a time, rather than retaining a second copy of all
    # sampled curves for the large zoo examples. Fractions retain exact phases.
    for side in (1, 0):
        for idx in reversed(range(len(groups[side]))):
            p, phase, _ = molecule.atoms[groups[side][idx]]
            curve = generator.generate_curve(system.Atom(p, phase), idx, side == 0)
            ax.plot(curve.x, curve.y, color=core.COLORS.get(p, "#666666"), lw=0.8)
    curve_legend(ax, molecule)
    fig.tight_layout()


def draw_radial(fig, molecule, highlight):
    generator = cp_pair_diagrams.CurveGenerator(n_thetas=4096)
    ax = fig.add_subplot()
    indices = Counter()
    for p, phase, _ in molecule.atoms:
        curve = generator.generate_curve(
            cp_pair_diagrams.Atom(p, float(phase)), indices[p]
        )
        indices[p] += 1
        ax.plot(curve.x, curve.y, color=core.COLORS.get(p, "#666666"), lw=0.8)
    curve_legend(ax, molecule)
    fig.tight_layout()


def draw_concentric(fig, molecule, highlight):
    core.circle(
        molecule.atoms,
        ax=fig.add_subplot(),
        title="",
        highlight=None if highlight < 0 else highlight,
    )


def draw_graph(fig, molecule, highlight):
    core.graph(molecule.atoms, ax=fig.add_subplot())


STRUCTURED_MAPS = {
    str(ROOT / "zoo/3711.md#3711_max"): example_3711.draw_structure,
    str(ROOT / "zoo/35711.md#35711_max590"): example_35711.draw_structure,
}


def draw_structure(fig, molecule, highlight):
    if molecule.target not in STRUCTURED_MAPS:
        raise ValueError(
            "There is no structured map for this molecule. The existing maps cover "
            "3711_max and 35711_max590; the curve and concentric views cover all molecules."
        )
    STRUCTURED_MAPS[molecule.target](fig)


@dataclass(frozen=True)
class Representation:
    name: str
    draw: Callable
    note: str


# Each drawer receives (figure, molecule, highlighted_atom). It owns only the
# figure contents, so adding a view needs no changes to the browser controls.
REPRESENTATIONS = (
    Representation(
        "In/out curves",
        draw_in_out,
        "Paired inward and outward curves. "
        "0B directions are preserved; 0A directions are inferred where possible.",
    ),
    Representation(
        "Radial curves",
        draw_radial,
        "A radial curve per atom, with a peak per site. "
        "Curves are schematic; crossings are not extra bonds.",
    ),
    Representation(
        "Concentric",
        draw_concentric,
        "One ring per atom. Sites at the same angle are bonded. "
        "Highlight an input atom index to trace its bonds.",
    ),
    Representation(
        "Bond graph",
        draw_graph,
        "Vertices are atoms; labels are input indices. "
        "Parallel bonds can overlap. Limited to 150 atoms for readability.",
    ),
    Representation(
        "Structured map",
        draw_structure,
        "Coordinate maps for 3711_max and 35711_max590.",
    ),
)


class ZooExplorer(QMainWindow):
    def __init__(self, molecules):
        super().__init__()
        self.molecules = molecules
        self.setWindowTitle("Molecule zoo")
        self.resize(1250, 850)
        self.render_timer = QTimer(self)
        self.render_timer.setSingleShot(True)
        self.render_timer.timeout.connect(self.render_current)

        sidebar = QWidget()
        side_layout = QVBoxLayout(sidebar)
        self.search = QLineEdit()
        self.search.setPlaceholderText("Filter by name or formula…")
        self.search.setClearButtonEnabled(True)
        side_layout.addWidget(self.search)
        self.list = QListWidget()
        self.list.setIconSize(QSize(56, 56))
        self.list.setMinimumWidth(285)
        for index, molecule in enumerate(molecules):
            item = QListWidgetItem(
                composition_icon(molecule, self.palette()),
                f"{molecule.formula}\n{molecule.name}",
            )
            item.setData(Qt.ItemDataRole.UserRole, index)
            item.setSizeHint(QSize(285, 76))
            item.setToolTip(
                f"{molecule.target}\n{len(molecule.atoms)} atoms\n"
                + ", ".join(f"{p}-atoms: {n}" for p, n in molecule.counts.items())
                + "\nThumbnail segments show atom counts by element."
            )
            self.list.addItem(item)
        side_layout.addWidget(self.list, 1)
        self.match_count = QLabel()
        side_layout.addWidget(self.match_count)
        navigation = QHBoxLayout()
        self.previous = QPushButton("← Previous")
        self.previous.setShortcut(QKeySequence("Alt+Left"))
        self.next = QPushButton("Next →")
        self.next.setShortcut(QKeySequence("Alt+Right"))
        navigation.addWidget(self.previous)
        navigation.addWidget(self.next)
        side_layout.addLayout(navigation)

        content = QWidget()
        layout = QVBoxLayout(content)
        self.formula = QLabel()
        font = self.formula.font()
        font.setPointSize(21)
        font.setBold(True)
        self.formula.setFont(font)
        self.formula.setTextInteractionFlags(
            Qt.TextInteractionFlag.TextSelectableByMouse
        )
        layout.addWidget(self.formula)
        self.summary = QLabel()
        self.summary.setWordWrap(True)
        layout.addWidget(self.summary)
        self.source = QLabel()
        self.source.setWordWrap(True)
        self.source.setTextInteractionFlags(
            Qt.TextInteractionFlag.TextSelectableByMouse
        )
        layout.addWidget(self.source)

        self.tabs = QTabBar()
        self.tabs.setExpanding(False)
        self.tabs.setDrawBase(False)
        for representation in REPRESENTATIONS:
            self.tabs.addTab(representation.name)
        layout.addWidget(self.tabs)
        self.note = QLabel()
        self.note.setWordWrap(True)
        layout.addWidget(self.note)
        highlight_row = QHBoxLayout()
        self.highlight_label = QLabel("Highlight atom")
        self.highlight = QSpinBox()
        self.highlight.setMinimum(-1)
        self.highlight.setSpecialValueText("None")
        self.highlight.setValue(-1)
        self.highlight.setToolTip(
            "Input-list index, starting at 0. None shows all rings."
        )
        highlight_row.addWidget(self.highlight_label)
        highlight_row.addWidget(self.highlight)
        highlight_row.addStretch()
        layout.addLayout(highlight_row)

        self.figure = Figure(figsize=(9, 7))
        self.canvas = FigureCanvasQTAgg(self.figure)
        self.toolbar = NavigationToolbar2QT(self.canvas, content)
        layout.addWidget(self.toolbar)
        self.message = QLabel()
        self.message.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.message.setWordWrap(True)
        layout.addWidget(self.message, 1)
        layout.addWidget(self.canvas, 1)

        splitter = QSplitter()
        splitter.addWidget(sidebar)
        splitter.addWidget(content)
        splitter.setStretchFactor(1, 1)
        splitter.setSizes([320, 930])
        self.setCentralWidget(splitter)

        self.search.textChanged.connect(self.filter_molecules)
        self.list.currentRowChanged.connect(self.select_molecule)
        self.tabs.currentChanged.connect(self.schedule_render)
        self.highlight.valueChanged.connect(self.schedule_render)
        self.previous.clicked.connect(lambda: self.step(-1))
        self.next.clicked.connect(lambda: self.step(1))
        self.filter_molecules()

    def visible_rows(self):
        return [i for i in range(self.list.count()) if not self.list.item(i).isHidden()]

    def filter_molecules(self):
        query = " ".join(self.search.text().lower().split())
        for row, molecule in enumerate(self.molecules):
            text = f"{molecule.name} {molecule.formula} {len(molecule.atoms)} atoms"
            self.list.item(row).setHidden(query not in " ".join(text.lower().split()))
        rows = self.visible_rows()
        self.match_count.setText(f"{len(rows)} / {len(self.molecules)} molecules")
        if not rows:
            self.list.setCurrentRow(-1)
        elif self.list.currentRow() not in rows:
            self.list.setCurrentRow(rows[0])
        self.update_navigation()

    def update_navigation(self):
        rows = self.visible_rows()
        self.previous.setEnabled(bool(rows) and self.list.currentRow() != rows[0])
        self.next.setEnabled(bool(rows) and self.list.currentRow() != rows[-1])

    def step(self, direction):
        rows = self.visible_rows()
        if self.list.currentRow() in rows:
            index = rows.index(self.list.currentRow()) + direction
            if 0 <= index < len(rows):
                self.list.setCurrentRow(rows[index])

    def select_molecule(self):
        self.update_navigation()
        row = self.list.currentRow()
        if row < 0:
            self.formula.clear()
            self.summary.clear()
            self.source.clear()
        else:
            molecule = self.molecules[row]
            self.formula.setText(molecule.formula)
            assignment = (
                "0B in/out directions preserved"
                if molecule.atoms[0][2] is not None
                else (
                    "0A · in/out assignment available"
                    if molecule.sides is not None
                    else "0A · no in/out assignment"
                )
            )
            self.summary.setText(
                f"{len(molecule.atoms)} atoms · {molecule.graph.number_of_edges()} bonds"
                f" · {assignment}"
            )
            path, _, section = molecule.target.partition("#")
            self.source.setText(f"{Path(path).name} · {section or molecule.name}")
            self.source.setToolTip(molecule.target)
            self.highlight.blockSignals(True)
            self.highlight.setMaximum(len(molecule.atoms) - 1)
            self.highlight.setValue(-1)
            self.highlight.blockSignals(False)
        self.schedule_render()

    def schedule_render(self):
        representation = REPRESENTATIONS[self.tabs.currentIndex()]
        self.note.setText(representation.note)
        concentric = representation.draw is draw_concentric
        self.highlight_label.setVisible(concentric)
        self.highlight.setVisible(concentric)
        self.message.setText("Rendering…")
        self.message.show()
        self.canvas.hide()
        self.toolbar.hide()
        # Collapse rapid selections and let Qt paint the new formula first.
        self.render_timer.start(40)

    def render_current(self):
        self.figure.clear()
        self.toolbar.update()
        row = self.list.currentRow()
        if row < 0:
            self.message.setText("No molecules match your filter.")
            return
        foreground = self.palette().color(QPalette.ColorRole.Text).name()
        background = self.palette().color(QPalette.ColorRole.Base).name()
        try:
            with mpl.rc_context(
                {
                    "text.color": foreground,
                    "axes.labelcolor": foreground,
                    "axes.edgecolor": foreground,
                    "xtick.color": foreground,
                    "ytick.color": foreground,
                    "axes.facecolor": background,
                    "figure.facecolor": background,
                    "savefig.facecolor": background,
                }
            ):
                self.figure.set_facecolor(background)
                REPRESENTATIONS[self.tabs.currentIndex()].draw(
                    self.figure, self.molecules[row], self.highlight.value()
                )
                self.canvas.draw()
        except Exception as error:
            # A failed/new renderer should leave molecule navigation usable.
            self.figure.clear()
            self.message.setText(str(error))
            self.statusBar().showMessage("This view could not be drawn.")
            return
        self.message.hide()
        self.canvas.show()
        self.toolbar.show()
        self.statusBar().showMessage(
            "Alt+← / Alt+→ browse molecules · Toolbar: zoom, pan, save"
        )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "targets", nargs="*", help="Markdown files, path.md#section, or JSON"
    )
    parser.add_argument(
        "--zoo", type=Path, default=ROOT / "zoo", help="Catalogue directory"
    )
    args = parser.parse_args()
    app = QApplication(sys.argv[:1])
    targets = []
    molecules = []
    failures = []
    for value in args.targets or [str(args.zoo)]:
        try:
            targets.extend(
                [value] if "#" in value else catalogue(Path(value).resolve())
            )
        except OSError as error:
            failures.append(f"{value}\n{error}")
    for target in dict.fromkeys(targets):
        try:
            molecules.append(Molecule.load(target))
        except (OSError, ValueError, SyntaxError, TypeError, KeyError) as error:
            failures.append(f"{target}\n{error}")
    if not molecules:
        QMessageBox.critical(
            None,
            "No molecules found",
            "\n\n".join(failures) or "No exact 0A/0B blocks found.",
        )
        return 1
    molecules.sort(
        key=lambda molecule: (len(molecule.atoms), molecule.formula, molecule.name)
    )
    window = ZooExplorer(molecules)
    window.show()
    if failures:
        QMessageBox.warning(
            window, "Some molecules could not be loaded", "\n\n".join(failures)
        )
    return app.exec()


if __name__ == "__main__":
    sys.exit(main())
