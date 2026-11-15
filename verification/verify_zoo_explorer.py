"""Headless rendering and navigation checks for the molecule zoo explorer.

Run: python verification/verify_zoo_explorer.py [--screenshots DIRECTORY]
"""

import argparse
import os
import sys
import tempfile
from pathlib import Path

os.environ["QT_QPA_PLATFORM"] = "offscreen"
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import matplotlib as mpl
import numpy as np
from matplotlib.collections import LineCollection
from PySide6.QtGui import QColor, QFont, QFontDatabase, QPalette
from PySide6.QtTest import QTest
from PySide6.QtWidgets import QApplication

import visualization.zoo_explorer as explorer

EXPECTED_SIZES = {
    "identical_twos": 2,
    "composite_224": 3,
    "two_and_five": 7,
    "235_ten": 10,
    "235_branches": 22,
    "2_3_5_max": 23,
    "example_0b": 30,
    "3711_max": 106,
    "35711_product": 552,
    "35711_mixed588": 588,
    "35711_max590": 590,
}


def settle(window, app):
    window.render_timer.stop()
    window.render_current()
    app.processEvents()


def check_renderers(window, app):
    rendered = 0
    for row, molecule in enumerate(window.molecules):
        original_atoms = list(molecule.atoms)
        assert len(molecule.atoms) == EXPECTED_SIZES[molecule.name]
        assert sum(molecule.counts.values()) == len(molecule.atoms)
        if molecule.sides is not None:
            assert all(
                molecule.sides[i] != molecule.sides[j]
                for i, j in molecule.graph.edges()
            )
        if molecule.atoms[0][2] is not None:
            assert molecule.sides == [atom[2] for atom in molecule.atoms]
        window.list.setCurrentRow(row)
        for index, representation in enumerate(explorer.REPRESENTATIONS):
            window.tabs.setCurrentIndex(index)
            settle(window, app)
            unavailable = (
                representation.draw is explorer.draw_graph and len(molecule.atoms) > 150
            ) or (
                representation.draw is explorer.draw_structure
                and molecule.target not in explorer.STRUCTURED_MAPS
            )
            if unavailable:
                assert not window.message.isHidden(), (
                    molecule.name,
                    representation.name,
                )
                assert window.canvas.isHidden()
            else:
                assert window.message.isHidden(), (
                    molecule.name,
                    representation.name,
                    window.message.text(),
                )
                assert window.figure.axes
                for ax in window.figure.axes:
                    for line in ax.lines:
                        assert np.isfinite(line.get_xydata()).all()
                rendered += 1
        assert molecule.atoms == original_atoms
        print(f"Checked {molecule.name}", flush=True)
    return rendered


def check_navigation(window, app):
    window.search.setText("5_3")
    assert len(window.visible_rows()) == 1
    assert window.molecules[window.list.currentRow()].name == "2_3_5_max"
    assert not window.previous.isEnabled() and not window.next.isEnabled()
    window.search.setText("2_15 3_5 5_3")
    assert len(window.visible_rows()) == 1
    assert window.molecules[window.list.currentRow()].name == "2_3_5_max"
    window.search.setText("no matching molecule")
    settle(window, app)
    assert window.list.currentRow() == -1
    assert window.formula.text() == ""
    assert window.message.text() == "No molecules match your filter."
    window.search.clear()
    window.tabs.setCurrentIndex(2)
    window.list.setCurrentRow(0)
    window.next.click()
    assert window.list.currentRow() == 1
    window.previous.click()
    assert window.list.currentRow() == 0
    assert not window.previous.isEnabled()
    window.highlight.setValue(1)
    settle(window, app)
    assert window.message.isHidden()
    assert len(window.figure.axes[0].lines) == 2
    window.list.setCurrentRow(len(window.molecules) - 1)
    assert window.highlight.maximum() == 589
    assert window.highlight.value() == -1
    assert not window.next.isEnabled()
    window.list.setCurrentRow(0)
    assert window.highlight.maximum() == 1
    # Fast selections must render only the most recent molecule and view.
    window.list.setCurrentRow(5)
    window.tabs.setCurrentIndex(3)
    QTest.qWait(70)
    assert not window.render_timer.isActive()
    assert window.message.isHidden()
    assert window.formula.text() == "2_15  3_5  5_3"


def check_custom_inputs():
    # The renderer's path#section syntax reserves '#'; Codex's Windows system
    # temporary path contains that character, so keep fixtures in the checkout.
    with tempfile.TemporaryDirectory(dir=explorer.ROOT) as temporary:
        directory = Path(temporary)
        (directory / "custom.md").write_text(
            "# Custom\n\n## pair\n\n```0A\n(2, 0), (2, 0),\n```\n",
            encoding="utf-8",
        )
        targets = explorer.catalogue(directory)
        assert len(targets) == 1
        molecule = explorer.Molecule.load(targets[0])
        assert molecule.formula == "2_2"
        (directory / "pair.json").write_text('[[2, "0"], [2, "0"]]')
        assert explorer.Molecule.load(directory / "pair.json").formula == "2_2"
        (directory / "invalid.json").write_text('[[2, "0"]]')
        try:
            explorer.Molecule.load(directory / "invalid.json")
        except ValueError:
            pass
        else:
            raise AssertionError("An invalid molecule was accepted")


def save_screenshots(window, app, directory):
    directory.mkdir(parents=True, exist_ok=True)
    for name, tab in (("2_3_5_max", 0), ("35711_max590", 4), ("3711_max", 3)):
        window.list.setCurrentRow(
            next(i for i, m in enumerate(window.molecules) if m.name == name)
        )
        window.tabs.setCurrentIndex(tab)
        settle(window, app)
        QTest.qWait(100)
        assert window.grab().save(str(directory / f"{name}.png"))

    original_palette = app.palette()
    palette = QPalette()
    for role in (QPalette.ColorRole.Window, QPalette.ColorRole.Button):
        palette.setColor(role, QColor("#303030"))
    palette.setColor(QPalette.ColorRole.Base, QColor("#202020"))
    for role in (
        QPalette.ColorRole.Text,
        QPalette.ColorRole.WindowText,
        QPalette.ColorRole.ButtonText,
    ):
        palette.setColor(role, QColor("#eeeeee"))
    app.setPalette(palette)
    dark_window = explorer.ZooExplorer(window.molecules)
    dark_window.show()
    dark_window.list.setCurrentRow(5)
    dark_window.tabs.setCurrentIndex(3)
    settle(dark_window, app)
    QTest.qWait(100)
    assert dark_window.grab().save(str(directory / "dark_graph.png"))
    ax = dark_window.figure.axes[0]
    # NetworkX draws multigraph edges as patches in newer releases and as a
    # line collection in older ones. Node collections are not bond colours.
    edge_colors = np.array(
        [patch.get_edgecolor() for patch in ax.patches]
        + [
            color
            for collection in ax.collections
            if isinstance(collection, LineCollection)
            for color in collection.get_edgecolors()
        ]
    )
    assert len(edge_colors) and np.all(edge_colors[:, :3] > 0.9)
    dark_window.close()
    app.setPalette(original_palette)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--screenshots", type=Path)
    args = parser.parse_args()
    app = QApplication([])
    # Qt's offscreen Windows plugin has no system fonts in the Codex environment.
    # Use Matplotlib's bundled font for QA; the real app keeps the system font.
    font_id = QFontDatabase.addApplicationFont(
        str(Path(mpl.get_data_path()) / "fonts/ttf/DejaVuSans.ttf")
    )
    assert font_id >= 0
    app.setFont(QFont(QFontDatabase.applicationFontFamilies(font_id)[0], 10))
    molecules = sorted(
        (explorer.Molecule.load(t) for t in explorer.catalogue(explorer.ROOT / "zoo")),
        key=lambda molecule: (len(molecule.atoms), molecule.formula, molecule.name),
    )
    assert {m.name for m in molecules} == set(EXPECTED_SIZES)
    window = explorer.ZooExplorer(molecules)
    window.show()
    app.processEvents()
    rendered = check_renderers(window, app)
    check_navigation(window, app)
    check_custom_inputs()
    if args.screenshots:
        save_screenshots(window, app, args.screenshots)
    window.close()
    print(
        f"Checked {len(molecules)} molecules, {rendered} rendered views, navigation and custom inputs."
    )


if __name__ == "__main__":
    main()
