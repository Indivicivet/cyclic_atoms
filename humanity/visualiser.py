import numpy as np
from dataclasses import dataclass
from matplotlib import colormaps
from matplotlib import pyplot as plt
from system import Rational, Atom



@dataclass
class CurveData:
    p: int
    x: np.ndarray
    y: np.ndarray
    col: np.ndarray = None

    def plot(self):
        if self.col is None:
            plt.plot(self.x, self.y)
            return
        plt.plot(self.x, self.y, color=self.col)


@dataclass
class CurveGenerator:
    n_up_atoms: int = 0
    n_down_atoms: int = 0
    n_thetas: int = 36000
    exp_dropoff: float = 70
    min_amp: float = 0.1
    amp_gap: float = 0.2
    max_amp: float = 1
    _thetas: np.ndarray = None
    _cos: np.ndarray = None
    _sin: np.ndarray = None

    def __post_init__(self):
        self._thetas = np.linspace(0, 2 * np.pi, self.n_thetas + 1)
        self._cos = np.sin(self._thetas)
        self._sin = np.cos(self._thetas)

    def generate_curve(self, atom: Atom, idx: int = 0, is_up: bool = True):
        base_amp = 0
        total_amp_range = self.max_amp - self.min_amp - self.amp_gap
        n_atoms = self.n_up_atoms + self.n_down_atoms

        mid_amp = (self.min_amp + self.max_amp + total_amp_range * (self.n_down_atoms - self.n_up_atoms) / n_atoms) / 2
        base_amp = self.max_amp if is_up else self.min_amp

        sin_amp = np.sin(atom.number * (self._thetas / 2 + atom.phase.numerator / atom.phase.denominator * np.pi))

        if True:
            base_amp += (-1 if is_up else 1) * total_amp_range * idx / n_atoms
            sin_amp = np.exp(-self.exp_dropoff / atom.number * np.abs(sin_amp))
        else:
            sin_amp *= sin_amp

        amps = base_amp + (mid_amp - base_amp) * sin_amp
        color = np.array(colormaps["hsv"]((atom.number * 0.73 + idx * 0.00) % 1))
        a = 0.7
        color *= a
        color += (1 - a) * np.ones(4)
        return CurveData(
            p=atom.number,
            x=amps * self._cos,
            y=amps * self._sin,
            col=color,
        )

    def generate_all_curves(self, atom_data: dict[int, tuple[list[int], list[int]]]):
        phase_space = int(np.lcm.reduce(list(atom_data.keys())))
        up_atoms = []
        down_atoms = []
        for number, offsets in atom_data.items():
            for up_offset in offsets[0]:
                up_atoms.append(Atom(number, Rational(up_offset, phase_space)))
            for down_offset in offsets[1]:
                down_atoms.append(Atom(number, Rational(down_offset, phase_space)))

        self.n_up_atoms = len(up_atoms)
        self.n_down_atoms = len(down_atoms)
        curves = []
        for i, atom in enumerate(up_atoms):
            curves.append(self.generate_curve(atom, idx=i, is_up=True))
        for i, atom in enumerate(down_atoms):
            curves.append(self.generate_curve(atom, idx=i, is_up=False))
        return curves


def plot_molecule_composition(composition: dict[int, tuple[list[int], list[int]]]):
    plt.style.use("dark_background")
    plt.figure(figsize=(8, 8))
    for curve in reversed(CurveGenerator().generate_all_curves(composition)):
        curve.plot()
    plt.axis("scaled")
    plt.gca().set_axis_off()
    plt.show()


if __name__ == "__main__":
    composition: dict[int, tuple[list[int], list[int]]] = {
        #5: [[0,14,28],[]],
        #3: [[],[0,14,28,42,56]]

        #5: [[0,-21],[]],
        #3: [[],[-7,-42]],
        #2: [[-7,-77],[0,-21,-63,-84]]

        # crap gpt
        #2: [[2], [0,1,3,4,6,9,10,13]],
        #3: [[1,3,5,9], [2]],
        #5: [[0,4], [5]]

        #7: [[0,135],[]],
        #5: [[10,157],[]],
        #3: [[],[0,45,150,175]],
        #2: [[70,80,140],[30,52,60,90,94,120,136,178,180]]

        #7: [[0,105],[]],
        #5: [[],[60,165]],
        #3: [[],[15,75,120,180]],
        #2: [[18,40,50,102,110,144,186,190],[0,30,90,150]]

        #2: [[2,8,11,14],[3,6,10,12,13,19]],
        #3: [[6,10,12],[1,7,9,11]],
        #7: [[1,3],[2]]

        # clod
        #5:  [[7,14,21,28,35,42,49,56,63,70],[11,22,33,44,55,66]],
        #7:  [[0,11,22,33,44],[]],
        #11: [[],[0,7,14,21,28]]

        # clod
        3:  [[35,70,105,140,175,210,245,280,315,350],[77,154,231,308]],
        5:  [[77,154],[33,66,99,132,165,198]],
        7:  [[0,33,66,99,132],[]],
        11: [[],[0,35,70]]

        #11: [[0,77,154],[]],
        #7: [[],[14,35,56,70,82,91,112,126,133,147,168,189,203,210,224]],
        #3: [[3,12,15,24,27,36,45,48,57,60,69,78,81,90,93,102,111,114,123,135,144,156,159,177,180,192,201,213,222,225],[0,21,42,63,84,105]]

        #11: [[0,38,39,50,72,77,115,116,127,149,154,171,193,204,226],[]],
        #7: [[],[28,35,105,112,182,189]],
        #3: [[6,90,138,222],[0,3,9,15,18,21,30,36,42,45,51,60,63,66,78,81,84,87,93,99,102,108,114,120,126,129,135,141,144,147,150,162,165,168,177,183,186,192,198,207,210,213,219,225,228]]

        #11: [[0,37,77,114,154,191],[]],
        #7: [[],[14,70,91,147,168,224]],
        #3: [[3,15,36,48,69,81,102,180,201,213],[0,9,21,30,42,51,63,72,84,93,105,126,156,177,189,198,210,219]]

        #11: [[0,99],[11,55,65,88,110,142,143,187,209,220]],
        #7: [[7,14,28,35,70,91,98,112,140,161,175,182,217,224],[0,42,126,210]],
        #3: [[9,27,33,45,60,66,75,89,93,108,111,132,144,159,165,174,177,192,198,207],[15,21,36,57,63,84,105,120,147,162,168,183,189,204]]

        #11: [[0,30,77,107,154,226],[]],
        #7: [[],[7,19,63,70,84,140,147,161,224]],
        #3: [[15,18,48,81,96,117,129,150,162,180,183,195,213,216,228],[0,9,21,42,72,93,105,126,135,156,168,177,189,198,210,219]]

        #11: [[0,51,77,128,154,226],[]],
        #7: [[],[35,40,49,56,70,84,112,126,133,147,189,194,203,210,224]],
        #3: [[12,15,18,24,27,45,48,57,60,78,81,90,111,117,123,144,150,159,180,183,192,213,216,222,225],[0,9,21,30,42,63,72,105,135,168,198,219]]

        #11: [[0,9,20,31,53,75,77,86,108,130,132,152,154,163,185,207,209,229,231,240,262,284,286,306,308,317,339,361,363,383],[]],
        #7: [[],[42,119,196,273,350]],
        #5: [[295],[0,5,10,25,30,35,40,45,55,60,65,70,80,90,95,100,105,110,115,125,135,140,145,150,160,165,170,175,180,195,200,205,210,215,220,230,235,245,250,255,265,270,275,280,285,290,300,305,310,315,320,325,335,340,345,355,360,370,375,380]]
    }

    plot_molecule_composition(composition)