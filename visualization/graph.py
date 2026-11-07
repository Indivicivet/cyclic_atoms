"""Bond graph. Usage: python visualization/graph.py zoo/235.md#2_3_5_max [out.png]"""

import argparse

import core

p = argparse.ArgumentParser(description=__doc__)
p.add_argument("input")
p.add_argument("output", nargs="?")
a = p.parse_args()
atoms = core.read_atoms(a.input)
core.describe(atoms)
core.graph(atoms, a.output)
