"""Interactive schematic of one molecule, with circular atom loops in 3D.

Run from the repository root: python visualization/wip_3d.py [path.md#section ...]
The default catalogue contains every molecule in zoo/. Geometry is a schematic;
exact phases determine contacts and cyclic order, not physical 3D coordinates.
"""

import argparse
import re
import sys
from collections import Counter, defaultdict
from functools import lru_cache
from pathlib import Path

import networkx as nx
import numpy as np
from PySide6.QtCore import Qt, QTimer
from PySide6.QtGui import QPalette
from PySide6.QtWidgets import (
    QApplication,
    QCheckBox,
    QDoubleSpinBox,
    QFileDialog,
    QHBoxLayout,
    QLabel,
    QListWidget,
    QMainWindow,
    QMessageBox,
    QPushButton,
    QSlider,
    QVBoxLayout,
    QWidget,
)

# Import the Qt canvas after PySide6 so Matplotlib uses the same Qt binding.
# isort: split
from matplotlib.backends.backend_qtagg import FigureCanvasQTAgg, NavigationToolbar2QT
from matplotlib.figure import Figure
from matplotlib.lines import Line2D
from mpl_toolkits.mplot3d.art3d import Line3DCollection

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import visualization.core as core


def catalogue():
    return [
        f"{path}#{heading}"
        for path in sorted((ROOT / "zoo").glob("*.md"))
        for heading in re.findall(
            r"^## (.+)\n\s*```0[AB]", path.read_text(encoding="utf-8"), re.MULTILINE
        )
    ]


@lru_cache(maxsize=24)
def load_molecule(target):
    atoms = core.read_atoms(target)
    occupancy, graph = core.analyze(atoms)
    positions = nx.spring_layout(graph, dim=3, seed=12, iterations=180)
    centres = np.array([positions[i] for i in range(len(atoms))])

    # Pull graph communities apart a little, so lobes joined through only a few
    # atoms have room in depth as well as in the screen plane.
    for group in nx.community.greedy_modularity_communities(graph):
        indices = sorted(group)
        centres[indices] += 0.65 * centres[indices].mean(axis=0)
    lengths = [np.linalg.norm(centres[i] - centres[j]) for i, j in graph.edges()]
    centres *= 3.0 / np.median(lengths)
    centres -= centres.mean(axis=0)

    parallel = defaultdict(list)
    for phase, owners in occupancy.items():
        parallel[tuple(sorted(owners))].append(phase)
    junctions = {}
    for (i, j), phases in parallel.items():
        perpendicular = np.cross(centres[j] - centres[i], [0.0, 0.0, 1.0])
        if np.linalg.norm(perpendicular) < 1e-10:
            perpendicular = np.array([1.0, 0.0, 0.0])
        perpendicular /= np.linalg.norm(perpendicular)
        for k, phase in enumerate(sorted(phases)):
            # Keep parallel contacts distinct, including when depth is zero.
            junctions[phase] = (centres[i] + centres[j]) / 2 + (
                k - (len(phases) - 1) / 2
            ) * 0.65 * perpendicular
    return atoms, occupancy, centres, junctions


def geometry(atoms, centres, junctions, radius, z_spacing):
    """Return closed atom curves passing through each exact shared junction.

    Scale centres and contacts in z before fitting ring planes. Scaling finished
    curves would squash circles into ellipses. Ports retain exact cyclic order;
    only a narrow interval around each port leaves the ring's circle.
    """
    scaled_centres = centres * [1.0, 1.0, z_spacing]
    scaled_junctions = {
        phase: position * [1.0, 1.0, z_spacing] for phase, position in junctions.items()
    }
    curves = []
    for atom, centre in zip(atoms, scaled_centres):
        phases = sorted(core.sites(atom))
        contacts = np.array([scaled_junctions[phase] for phase in phases])
        if radius == 0:
            # Each spoke is traversed out and back as the atom loop collapses.
            curves.append(
                np.concatenate(
                    [np.array([centre, contact, centre]) for contact in contacts]
                )
            )
            continue

        angles = 2 * np.pi * np.array([float(phase) for phase in phases])
        directions = contacts - centre
        directions /= np.maximum(np.linalg.norm(directions, axis=1)[:, None], 1e-10)
        port_vectors = np.column_stack((np.cos(angles), np.sin(angles)))
        # Orthogonal Procrustes fits a circular plane without permuting ports.
        # A small XY preference resolves rank-one fits (notably two-atoms), and
        # makes z=0 genuinely flat even for those otherwise ambiguous planes.
        left, _, right = np.linalg.svd(
            port_vectors.T @ directions + 0.08 * np.eye(2, 3), full_matrices=False
        )
        frame = left @ right
        half_gap = 0.18 * 2 * np.pi / atom[0]
        pieces = []
        for k, (angle, contact) in enumerate(zip(angles, contacts)):
            next_angle = angles[k + 1] if k + 1 < len(angles) else angles[0] + 2 * np.pi
            boundaries = np.array([angle - half_gap, angle + half_gap])
            ends = (
                centre
                + radius
                * np.column_stack((np.cos(boundaries), np.sin(boundaries)))
                @ frame
            )
            tangents = (
                radius
                * np.column_stack((-np.sin(boundaries), np.cos(boundaries)))
                @ frame
            )
            # A quadratic excursion on either side meets the exact contact.
            # End tangents agree with the circle; both partners share one point.
            t = np.linspace(0, 1, 10)[:, None]
            pieces.extend(
                [
                    (1 - t) ** 2 * ends[0]
                    + 2 * (1 - t) * t * (ends[0] + half_gap * tangents[0])
                    + t**2 * contact,
                    (1 - t) ** 2 * contact
                    + 2 * (1 - t) * t * (ends[1] - half_gap * tangents[1])
                    + t**2 * ends[1],
                ]
            )
            arc = np.linspace(angle + half_gap, next_angle - half_gap, 28)
            pieces.append(
                centre + radius * np.column_stack((np.cos(arc), np.sin(arc))) @ frame
            )
        curve = np.concatenate(pieces)
        curves.append(np.vstack((curve, curve[0])))
    return scaled_centres, scaled_junctions, curves


class Slider(QSlider):
    def wheelEvent(self, event):
        event.ignore()


class MoleculeViewer(QMainWindow):
    def __init__(self, targets):
        super().__init__()
        self.setWindowTitle("Cyclic atoms · 3D")
        self.resize(1320, 900)
        self.molecule = None
        self.labels = []
        self.figure = Figure(layout="constrained")
        self.canvas = FigureCanvasQTAgg(self.figure)
        self.axes = self.figure.add_subplot(projection="3d")
        background = self.palette().color(QPalette.ColorRole.Window).name()
        self.foreground = self.palette().color(QPalette.ColorRole.WindowText).name()
        self.figure.set_facecolor(background)
        self.axes.set_facecolor(background)
        self.axes.set_axis_off()
        self.axes.set_proj_type("persp")
        self.axes.view_init(elev=24, azim=-55)

        central = QWidget()
        self.setCentralWidget(central)
        layout = QHBoxLayout(central)
        controls_widget = QWidget()
        controls_widget.setFixedWidth(265)
        controls = QVBoxLayout(controls_widget)
        layout.addWidget(controls_widget)
        plot = QVBoxLayout()
        layout.addLayout(plot, stretch=1)
        plot.addWidget(self.canvas, stretch=1)
        plot.addWidget(NavigationToolbar2QT(self.canvas, self))

        controls.addWidget(QLabel("Molecule"))
        self.molecules = QListWidget()
        controls.addWidget(self.molecules, stretch=1)
        self.targets = []
        for target in targets:
            self.add_target(target)
        open_button = QPushButton("Open molecule file…")
        open_button.clicked.connect(self.open_file)
        controls.addWidget(open_button)
        self.summary = QLabel()
        self.summary.setWordWrap(True)
        controls.addWidget(self.summary)

        self.radius = self.add_parameter(controls, "Ring radius", 0, 2, 0.65)
        self.depth = self.add_parameter(controls, "Z spacing", 0, 5, 1)
        self.show_labels = QCheckBox("Atom indices")
        self.show_contacts = QCheckBox("Bond junction dots")
        controls.addWidget(self.show_labels)
        controls.addWidget(self.show_contacts)
        self.show_labels.toggled.connect(self.schedule_draw)
        self.show_contacts.toggled.connect(self.schedule_draw)
        reset_button = QPushButton("Reset view")
        reset_button.clicked.connect(self.reset_view)
        controls.addWidget(reset_button)
        help_text = QLabel(
            "Drag to rotate · scroll to zoom\n\n"
            "Dots are atoms. Coloured loops follow each atom's cyclic sites; "
            "two loops meet at each bond. Crossings elsewhere are not bonds.\n\n"
            "Radius 0 gives the bond graph. Z spacing 0 flattens the drawing.\n\n"
            "Schematic layout, not physical coordinates."
        )
        help_text.setWordWrap(True)
        controls.addWidget(help_text)

        # Coalesce slider events rather than queuing a full redraw for each tick.
        self.redraw_timer = QTimer(self)
        self.redraw_timer.setSingleShot(True)
        self.redraw_timer.setInterval(25)
        self.redraw_timer.timeout.connect(self.draw_molecule)
        self.last_parameters = None
        self.molecules.currentRowChanged.connect(self.select_molecule)
        default = next(
            (
                i
                for i, target in enumerate(self.targets)
                if target.endswith("#235_branches")
            ),
            0,
        )
        self.molecules.setCurrentRow(default)
        self.canvas.mpl_connect("scroll_event", self.zoom)

    def add_target(self, target):
        self.targets.append(str(target))
        path, _, section = str(target).partition("#")
        self.molecules.addItem(section or Path(path).stem)
        self.molecules.item(len(self.targets) - 1).setToolTip(str(target))

    def add_parameter(self, controls, name, minimum, maximum, value):
        row = QHBoxLayout()
        row.addWidget(QLabel(name))
        spin = QDoubleSpinBox()
        spin.setRange(minimum, maximum)
        spin.setDecimals(2)
        spin.setSingleStep(0.05)
        spin.setValue(value)
        row.addWidget(spin)
        controls.addLayout(row)
        slider = Slider(Qt.Orientation.Horizontal)
        slider.setRange(round(minimum * 100), round(maximum * 100))
        slider.setValue(round(value * 100))
        slider.valueChanged.connect(lambda tick: spin.setValue(tick / 100))
        spin.valueChanged.connect(lambda number: slider.setValue(round(number * 100)))
        spin.valueChanged.connect(self.schedule_draw)
        controls.addWidget(slider)
        return spin

    def schedule_draw(self, *_):
        self.redraw_timer.start()

    def select_molecule(self, index):
        if index < 0:
            return
        try:
            molecule = load_molecule(self.targets[index])
        except (OSError, ValueError, SyntaxError) as error:
            QMessageBox.warning(self, "Cannot open molecule", str(error))
            return
        self.molecule = molecule
        atoms, occupancy, _, _ = molecule
        self.summary.setText(
            f"{len(atoms)} atoms · {len(occupancy)} bonds\n"
            + "   ".join(
                f"{p}: {n}" for p, n in sorted(Counter(a[0] for a in atoms).items())
            )
        )
        self.draw_molecule(fit=True)

    def open_file(self):
        path, _ = QFileDialog.getOpenFileName(
            self, "Open molecule", str(ROOT / "zoo"), "Molecules (*.md *.json)"
        )
        if not path:
            return
        try:
            text = Path(path).read_text(encoding="utf-8")
        except OSError as error:
            QMessageBox.warning(self, "Cannot open file", str(error))
            return
        sections = re.findall(r"^## (.+)\n\s*```0[AB]", text, re.MULTILINE)
        first = len(self.targets)
        for target in [f"{path}#{section}" for section in sections] or [path]:
            self.add_target(target)
        self.molecules.setCurrentRow(first)

    def draw_molecule(self, fit=False):
        if self.molecule is None:
            return
        atoms, _, base_centres, base_junctions = self.molecule
        centres, junctions, curves = geometry(
            atoms, base_centres, base_junctions, self.radius.value(), self.depth.value()
        )
        # Removing artists keeps the user's camera angle and zoom intact.
        for artist in list(self.axes.collections) + self.labels:
            artist.remove()
        self.labels = []
        colors = [core.COLORS.get(atom[0], "#666666") for atom in atoms]
        self.axes.add_collection3d(
            Line3DCollection(curves, colors=colors, linewidths=1.2), autolim=False
        )
        self.axes.scatter(*centres.T, c=colors, s=22, depthshade=False)
        if self.show_contacts.isChecked():
            self.axes.scatter(
                *np.array(list(junctions.values())).T,
                color="gray",
                s=10,
                depthshade=False,
            )
        if self.show_labels.isChecked():
            self.labels = [
                self.axes.text(*centre, f" {i}", fontsize=8, color=self.foreground)
                for i, centre in enumerate(centres)
            ]
        parameters = (self.radius.value(), self.depth.value())
        if fit or parameters != self.last_parameters:
            self.fit_geometry(curves)
        self.last_parameters = parameters
        if fit:
            elements = sorted({atom[0] for atom in atoms})
            self.axes.legend(
                handles=[
                    Line2D(
                        [0], [0], color=core.COLORS.get(p, "#666666"), label=f"{p}-atom"
                    )
                    for p in elements
                ],
                loc="upper left",
                frameon=False,
                labelcolor=self.foreground,
            )
        self.canvas.draw_idle()

    def fit_geometry(self, curves):
        points = np.concatenate(curves)
        midpoint = (points.max(axis=0) + points.min(axis=0)) / 2
        half_width = max(np.ptp(points, axis=0).max() * 0.57, 1)
        for setter, coordinate in zip(
            (self.axes.set_xlim, self.axes.set_ylim, self.axes.set_zlim), midpoint
        ):
            setter(coordinate - half_width, coordinate + half_width)
        self.axes.set_box_aspect((1, 1, 1), zoom=1.3)

    def reset_view(self):
        self.axes.view_init(elev=24, azim=-55)
        self.draw_molecule(fit=True)

    def zoom(self, event):
        if event.inaxes != self.axes:
            return
        scale = 0.88 if event.button == "up" else 1 / 0.88
        for getter, setter in (
            (self.axes.get_xlim, self.axes.set_xlim),
            (self.axes.get_ylim, self.axes.set_ylim),
            (self.axes.get_zlim, self.axes.set_zlim),
        ):
            low, high = getter()
            midpoint = (low + high) / 2
            setter(
                midpoint + (low - midpoint) * scale,
                midpoint + (high - midpoint) * scale,
            )
        self.canvas.draw_idle()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "molecules", nargs="*", help="0A/0B JSON or Markdown path#section"
    )
    args = parser.parse_args()
    app = QApplication(sys.argv[:1])
    window = MoleculeViewer(args.molecules or catalogue())
    window.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
