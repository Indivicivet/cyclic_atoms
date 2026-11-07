import math
from system import Rational, Atom, Molecule



def get_atom_phases(atoms: list[Atom]) -> dict[int, list[Rational]]:
    phases: dict[int, list[Rational]] = {}
    for atom in atoms:
        if atom.number not in phases:
            phases[atom.number] = []
        phases[atom.number].append(atom.phase)
    return dict(sorted(phases.items()))

def get_phase_indices(phases: list[Rational], phase_space: int) -> list[int]:
    phase_indices = []
    for phase in phases:
        phase_indices.append(int(phase.numerator * phase_space / phase.denominator))
    return phase_indices

def get_phase_index_composition(molecule: Molecule) -> dict[int, tuple[list[int], list[int]]]:
    composition: dict[int, tuple[list[int], list[int]]] = {}
    up_phases = get_atom_phases(molecule.up_atoms)
    down_phases = get_atom_phases(molecule.down_atoms)
    numbers = []
    for number in up_phases.keys():
        if number not in numbers:
            numbers.append(number)
        if number not in down_phases:
            down_phases[number] = []
    for number in down_phases.keys():
        if number not in numbers:
            numbers.append(number)
        if number not in up_phases:
            up_phases[number] = []
    phase_space = int(math.lcm(*list(numbers)))
    for number in sorted(numbers, reverse=True):
        composition[number] = (get_phase_indices(up_phases[number], phase_space), get_phase_indices(down_phases[number], phase_space))
    return composition

def phase_index_composition_to_str(composition: dict[int, tuple[list[int], list[int]]]) -> str:
    string = ""
    for number, phase_indices in composition.items():
        string += f"{number}: ["
        string += f"[{",".join(map(str, sorted(phase_indices[0])))}],"
        string += f"[{",".join(map(str, sorted(phase_indices[1])))}]"
        string = string.rstrip(",") + "],\n"
    return string

def convert_to_superscript(number: int) -> str:
    return ''.join("⁰¹²³⁴⁵⁶⁷⁸⁹"[int(digit)] for digit in str(number))

def convert_to_subscript(number: int) -> str:
    return ''.join("₀₁₂₃₄₅₆₇₈₉"[int(digit)] for digit in str(number))

def get_composition_short_str(up_atoms: list[Atom], down_atoms: list[Atom]) -> str:
    composition = ""
    num_atoms = 0
    num_peaks = 0
    up_phases = get_atom_phases(up_atoms)
    down_phases = get_atom_phases(down_atoms)
    up_counts: dict[int, int] = {}
    down_counts: dict[int, int] = {}
    for number, phases in up_phases.items():
        num_atoms += len(phases)
        num_peaks += number * len(phases)
        up_counts[number] = len(phases)
        down_counts[number] = 0
    for number, phases in down_phases.items():
        num_atoms += len(phases)
        num_peaks += number * len(phases)
        down_counts[number] = len(phases)
        if number not in up_counts:
            up_counts[number] = 0
    for number in sorted(up_counts.keys(), reverse=True):
        composition += str(number)
        if up_counts[number]:
            composition += convert_to_superscript(up_counts[number])
        if down_counts[number]:
            composition += convert_to_subscript(down_counts[number])
    return F"{composition} ({num_atoms}, {num_peaks})"