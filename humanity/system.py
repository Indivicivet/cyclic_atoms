import math
import random



class Rational:
    def __init__(self, numerator: int, denominator: int):
        gcd = math.gcd(numerator, denominator)
        self.numerator: int = numerator // gcd
        self.denominator: int = denominator // gcd

    def __add__(self, other):
        new_numerator = self.numerator * other.denominator + other.numerator * self.denominator
        new_denominator = self.denominator * other.denominator
        gcd = math.gcd(new_numerator, new_denominator)
        new_numerator //= gcd
        new_denominator //= gcd
        new_numerator = new_numerator % new_denominator # only interested in rationals between 0 and 1
        return Rational(new_numerator, new_denominator)
    
    def __eq__(self, other):
        return self.numerator == other.numerator and self.denominator == other.denominator

    def __lt__(self, other):
        return self.numerator * other.denominator < other.numerator * self.denominator

    def __str__(self):
        return f"{self.numerator}/{self.denominator}"

def get_phases(number: int, phase: Rational) -> list[Rational]:
    return [phase + Rational(i, number) for i in range(number)]


class Atom:
    def __init__(self, number: int, phase: Rational):
        self.number: int = number
        self.phase: Rational = phase

def find_unpaired_peak_for_new_atom(new_atom_number: int, aligned_peaks: list[Rational], opposite_atoms: list[Atom]) -> Rational | None:
    for opposite_atom in opposite_atoms:
        for opposite_atom_phase in get_phases(opposite_atom.number, opposite_atom.phase):
            can_add_atom = True
            for new_atom_phase in get_phases(new_atom_number, opposite_atom_phase):
                if new_atom_phase in aligned_peaks:
                    # this opposite atom phase won't work for this new atom because there is already an atom with a peak at this phase
                    can_add_atom = False
                    break
            if can_add_atom:
                # all the peak phases for this new_atom are free, we can add it
                return opposite_atom_phase
    return None

class Molecule:
    def __init__(self, initial_up_atom_number: int):
        self.up_atoms: list[Atom] = []
        self.down_atoms: list[Atom] = []
        self.up_peaks = []
        self.down_peaks = []
        self.add_up_atom(Atom(initial_up_atom_number, Rational(0, 1)))

    def all_peaks_paired(self) -> bool:
        for up_atom in self.up_atoms:
            for up_phase in get_phases(up_atom.number, up_atom.phase):
                if up_phase not in self.down_peaks:
                    return False
        for down_atom in self.down_atoms:
            for down_phase in get_phases(down_atom.number, down_atom.phase):
                if down_phase not in self.up_peaks:
                    return False
        return True

    def add_up_atom(self, up_atom: Atom):
        self.up_atoms.append(up_atom)
        for p in get_phases(up_atom.number, up_atom.phase):
            self.up_peaks.append(p)

    def add_down_atom(self, down_atom: Atom):
        down_atom = Atom(down_atom.number, down_atom.phase)
        self.down_atoms.append(down_atom)
        for p in get_phases(down_atom.number, down_atom.phase):
            self.down_peaks.append(p)

    def can_add_atom(self, new_atom_numbers: list[int]) -> bool:
        for new_atom_number in new_atom_numbers:
            phase_for_new_up_atom = find_unpaired_peak_for_new_atom(new_atom_number, self.up_peaks, self.down_atoms)
            if phase_for_new_up_atom is not None:
                return True
            phase_for_new_down_atom = find_unpaired_peak_for_new_atom(new_atom_number, self.down_peaks, self.up_atoms)
            if phase_for_new_down_atom is not None:
                return True
        return False

    def try_add_atom(self, new_atom_number: int) -> bool:
        upnesses: list[bool] = []
        phase_for_new_up_atom = find_unpaired_peak_for_new_atom(new_atom_number, self.up_peaks, self.down_atoms)
        if phase_for_new_up_atom is not None:
            upnesses.append(True)
        phase_for_new_down_atom = find_unpaired_peak_for_new_atom(new_atom_number, self.down_peaks, self.up_atoms)
        if phase_for_new_down_atom is not None:
            upnesses.append(False)
        if len(upnesses) > 0:
            if random.choice(upnesses):
                self.add_up_atom(Atom(new_atom_number, phase_for_new_up_atom))
            else:
                self.add_down_atom(Atom(new_atom_number, phase_for_new_down_atom))
        return len(upnesses) > 0

    def __str__(self):
        up_atoms_str = ', '.join([f"({atom.number}, {atom.phase})" for atom in self.up_atoms])
        down_atoms_str = ', '.join([f"({atom.number}, {atom.phase})" for atom in self.down_atoms])
        return f"Molecule(Up Atoms: [{up_atoms_str}], Down Atoms: [{down_atoms_str}])"