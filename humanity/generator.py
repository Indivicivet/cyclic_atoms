import random
from system import Molecule
from string_utils import get_phase_index_composition, phase_index_composition_to_str, get_composition_short_str
from visualiser import plot_molecule_composition



atomic_distribution: dict[int, float] = {
    #1: 1/1.0,
    2: 1/2.0,
    3: 1/3.0,
    #4: 1/4.0,
    #5: 1/5.0,
    #6: 1/6.0,
    #7: 1/7.0,
    #8: 1/8.0,
    #9: 1/9.0,
    #10: 1/10.0,
    11: 1/11.0
}

def random_atom_number() -> int:
    rand = random.random()
    distribution_sum = sum(atomic_distribution.values())
    cumulative = 0.0
    for number, probability in atomic_distribution.items():
        probability /= distribution_sum
        cumulative += probability
        if rand < cumulative:
            return number
    return list(atomic_distribution.keys())[0]


if __name__ == "__main__":
    while True:
        molecule = Molecule(list(atomic_distribution.keys())[-1])
        molecule_completed = False
        while True:
            if molecule.can_add_atom(list(atomic_distribution.keys())):
                molecule.try_add_atom(random_atom_number())
            else:
                # remove some of the uncompleted atoms to try again
                #for i in range(random.randint(1, 1 + (len(molecule.up_atoms) + len(molecule.down_atoms)) // 2)):
                #    molecule.remove_random_uncompleted_atom()
                break
            if molecule.all_peaks_paired():
                break
        composition = get_phase_index_composition(molecule)
        if (len(composition) > 2 and molecule.all_peaks_paired()):
            print(get_composition_short_str(molecule.up_atoms, molecule.down_atoms) + (" completed:" if molecule.all_peaks_paired() else " failed to complete:"))
            print(phase_index_composition_to_str(composition) + "\n")
            plot_molecule_composition(composition)