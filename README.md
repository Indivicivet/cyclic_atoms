# Cyclic atoms

This is a maths / imaginary physics project investigating the properties of hypothetical "atoms" consisting of cyclic groups where each element must join to exactly one element of another cyclic group.

# Repo structure

## [README.md](README.md)

high level overview of file structure

## [INTRO.md](INTRO.md)

introduction to nomenclature, definitions, basic examples and basic properties

this includes definition of unambiguous text formats for representing molecules

## [THEORY.md](THEORY.md)

proven mathematical results, existence results, bounds, and conjectures for results

## [CHEMISTRY.md](CHEMISTRY.md) and [chemistry/](chemistry/)

open configurations, cutting and joining molecules, binary reaction recipes, a three-prime parity classification, and reaction graph plots. Run `python -m chemistry.examples` to generate the plots, `python -m chemistry.verify` to run the checks, and `python -m chemistry.minimum_split` for the 140-cut splitting of three maximum 3-5-7 molecules.

## [zoo/](zoo/)

examples of various structures in exact 0A and 0B notation

## [visualization/](visualization/)

scripts to visualize atoms and molecules in various ways (direct, pretty, topological, etc)

## [lean/](lean/)

formalized proofs in lean (TODO expand)

## [verification/](verification/)

scratch scripts for verification

## [humanity/](humanity/)

human-written scripts, musings, etc.
