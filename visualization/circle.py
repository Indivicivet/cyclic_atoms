"""Concentric view. Usage: python visualization/circle.py zoo/23_max.md out.png"""

import argparse

import core

p = argparse.ArgumentParser(description=__doc__)
p.add_argument("input")
p.add_argument("output")
p.add_argument("--highlight", type=int, default=0)
a = p.parse_args()
atoms = core.read_atoms(a.input)
core.describe(atoms)
core.circle(atoms, a.output, highlight=a.highlight)
