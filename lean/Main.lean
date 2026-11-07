import CyclicAtoms

open CyclicAtoms

def main : IO Unit := do
  IO.println s!"M(2, 3, 5) = {maxThreePrimes 2 3 5}"
  IO.println s!"M(3, 7, 11) = {maxThreePrimes 3 7 11}"
  IO.println s!"C(3, 5, 7, 11) = {fourPrimeConstructionSize 3 5 7 11}"
