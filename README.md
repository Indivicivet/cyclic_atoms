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

open configurations, cutting and joining molecules, exact binary reaction
recipes, a three-prime parity classification, and graph plots of reactions.
Run `python -m chemistry.examples` to regenerate the artifacts and
`python -m chemistry.verify` to check the results.

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
