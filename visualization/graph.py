"""Bond graph. Usage: python visualization/graph.py zoo/23_max.md out.png"""

import argparse
from core import read_atoms, describe, graph

p = argparse.ArgumentParser(description=__doc__)
p.add_argument("input")
p.add_argument("output")
a = p.parse_args()
atoms = read_atoms(a.input)
describe(atoms)
graph(atoms, a.output)
