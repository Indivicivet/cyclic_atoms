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

## [CHEMISTRY.md](CHEMISTRY.md), [CLOSED_CHEMISTRY.md](CLOSED_CHEMISTRY.md), [SYNTHESIS.md](SYNTHESIS.md), [UNIVERSAL_SYNTHESIS.md](UNIVERSAL_SYNTHESIS.md), and [chemistry/](chemistry/)

open configurations, cutting and joining molecules, closed-state reactions, shortest syntheses, universal binary synthesis, and reaction plots. Generated figures and JSON outputs are written to `chemistry/output/` (gitignored). On a fresh clone, generate them and run the checks with:

```sh
python -m chemistry.examples
python -m chemistry.minimum_split
python -m chemistry.closed_reactions
python -m chemistry.synthesis
python -m chemistry.synthesis_plots
python -m chemistry.universal_synthesis
python -m chemistry.verify
```

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
