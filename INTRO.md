# Cyclic atoms

# Basic definitions

...

# Atom notation

## Notation 0A

Notation 0A is a list of tuples (or length 2 lists), each one consisting of a cyclic group length and an offset in turns, as used by humanity/cp_pair_diagrams.py, e.g.

[2, 0], [2, 1 / 4], [4, 0]  # 4 isn't prime but it's an easy example

or

[5, 0],
[5, 1 / 10],
*[[2, i / 10] for i in range(5)]

which represents the unique connected molecule with atom set {2, 5}

## Notation 0B

Notation 0B is a python dict[tuple[list[int], list[int]]] where the dict keys represent the base cyclic group length (prime p) and the two lists are the "outward facing" and "inward facing" indices of the identity of the group, where numbers go from {0, ..., p1p2p3...pn - 1}, where p_i are all of the primes, e.g.

3: [[35,70,105,140,175,210,245,280,315,350],[77,154,231,308]]
5: [[77,154],[33,66,99,132,165,198]]
7: [[0,33,66,99,132],[]]
11: [[],[0,35,70]]

in this case the numbers go from 0 to 3*5*7*11 - 1.

