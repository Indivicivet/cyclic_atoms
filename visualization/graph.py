"""Bond graph. Usage: python visualization/graph.py zoo/23_max.md out.png"""

import argparse

import core

p = argparse.ArgumentParser(description=__doc__)
p.add_argument("input")
p.add_argument("output")
a = p.parse_args()
atoms = core.read_atoms(a.input)
core.describe(atoms)
core.graph(atoms, a.output)
