"""Concentric view. Usage: python visualization/circle.py zoo/23_max.json out.png"""
import argparse
from core import read_atoms, describe, circle
p=argparse.ArgumentParser(description=__doc__); p.add_argument('input'); p.add_argument('output'); p.add_argument('--highlight',type=int,default=0); a=p.parse_args()
atoms=read_atoms(a.input); describe(atoms); circle(atoms,a.output,highlight=a.highlight)
