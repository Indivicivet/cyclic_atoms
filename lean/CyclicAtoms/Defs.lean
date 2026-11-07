namespace CyclicAtoms

/-- A rational phase on the unit circle ℝ/ℤ, represented as `num / den` in turns. -/
structure Phase where
  num : Nat
  den : Nat
  den_pos : den > 0
  deriving Repr

namespace Phase

/-- Zero phase (0 turns). -/
def zero : Phase := ⟨0, 1, Nat.zero_lt_one⟩

/-- Phase `k / n` in turns for `n > 0`. -/
def ofRat (k : Nat) (n : Nat) (h : n > 0) : Phase := ⟨k, n, h⟩

/-- Sum of two phases in turns. -/
def add (a b : Phase) : Phase :=
  ⟨a.num * b.den + b.num * a.den,
   a.den * b.den,
   Nat.mul_pos a.den_pos b.den_pos⟩

/-- Reflection (`1 - (num % den) / den`) of a phase across 0 on the unit circle. -/
def neg (a : Phase) : Phase :=
  ⟨a.den - a.num % a.den, a.den, a.den_pos⟩

/-- Two phases represent the same point on the circle `ℝ/ℤ` (`mod 1`) iff
`(n₁ * d₂) mod (d₁ * d₂) = (n₂ * d₁) mod (d₁ * d₂)`. -/
def Equiv (a b : Phase) : Prop :=
  (a.num * b.den) % (a.den * b.den) = (b.num * a.den) % (a.den * b.den)

theorem equiv_refl (a : Phase) : Equiv a a := rfl

theorem equiv_symm {a b : Phase} (h : Equiv a b) : Equiv b a := by
  unfold Equiv at *
  rw [Nat.mul_comm b.den a.den]
  exact h.symm

end Phase

/-- Divisibility on `Nat`. -/
def Divides (d n : Nat) : Prop :=
  ∃ k : Nat, n = d * k

/-- Primality predicate on `Nat`: `p ≥ 2` and the only divisors of `p` are `1` and `p`. -/
def IsPrime (p : Nat) : Prop :=
  p ≥ 2 ∧ ∀ d : Nat, Divides d p → d = 1 ∨ d = p

/-- [Atom] An atom `(p, phase)` has element `p ≥ 2` and phase `phase` in turns. -/
structure Atom where
  p : Nat
  phase : Phase
  h_p : p ≥ 2
  deriving Repr

namespace Atom

theorem p_pos (A : Atom) : A.p > 0 :=
  Nat.lt_of_lt_of_le (by decide : 0 < 2) A.h_p

/-- Whether an atom has a prime element `p`. -/
def IsPrimeAtom (A : Atom) : Prop :=
  IsPrime A.p

/-- The `k`-th point of atom `A = (p, a)`, at `a + k/p` turns, for `k ∈ {0, ..., p - 1}`. -/
def point (A : Atom) (k : Fin A.p) : Phase :=
  Phase.add A.phase (Phase.ofRat k.val A.p A.p_pos)

/-- Point `x` on the circle belongs to atom `A` if it equals `A.point k (mod 1)` for some `k`. -/
def hasPoint (A : Atom) (x : Phase) : Prop :=
  ∃ k : Fin A.p, Phase.Equiv x (A.point k)

/-- Rotate atom `A` by `θ` turns. -/
def rotate (θ : Phase) (A : Atom) : Atom :=
  ⟨A.p, Phase.add A.phase θ, A.h_p⟩

/-- Reflect atom `A` across phase 0. -/
def reflect (A : Atom) : Atom :=
  ⟨A.p, Phase.neg A.phase, A.h_p⟩

/-- Two atoms have identical point sets on the circle. -/
def SamePoints (A B : Atom) : Prop :=
  ∀ x : Phase, A.hasPoint x ↔ B.hasPoint x

theorem samePoints_refl (A : Atom) : SamePoints A A := by
  intro x
  exact Iff.rfl

theorem samePoints_symm {A B : Atom} (h : SamePoints A B) : SamePoints B A := by
  intro x
  exact (h x).symm

theorem samePoints_trans {A B C : Atom} (h1 : SamePoints A B) (h2 : SamePoints B C) :
    SamePoints A C := by
  intro x
  exact Iff.trans (h1 x) (h2 x)

end Atom

/-- [Configuration] A finite collection (multiset represented as a list of indexed vertices) of atoms. -/
abbrev Config := List Atom

namespace Config

/-- [Size] The size of a configuration is the total number of atoms. -/
def size (C : Config) : Nat := C.length

/-- Rotate an entire configuration by `θ` turns. -/
def rotate (θ : Phase) (C : Config) : Config :=
  C.map (Atom.rotate θ)

/-- Reflect an entire configuration across 0. -/
def reflect (C : Config) : Config :=
  C.map Atom.reflect

/-- Two configurations have the same atoms up to a bijection of their indices
that preserves elements and point sets. -/
def Equiv (C₁ C₂ : Config) : Prop :=
  ∃ (f : Fin C₁.length → Fin C₂.length) (g : Fin C₂.length → Fin C₁.length),
    (∀ i, g (f i) = i) ∧
    (∀ j, f (g j) = j) ∧
    (∀ i, (C₁.get i).p = (C₂.get (f i)).p ∧ Atom.SamePoints (C₁.get i) (C₂.get (f i)))

/-- Two configurations are equivalent up to rotation (`RotEquiv`). -/
def RotEquiv (C₁ C₂ : Config) : Prop :=
  ∃ θ : Phase, Equiv (rotate θ C₁) C₂

/-- A configuration is chiral if it is not rotationally equivalent to its reflection. -/
def IsChiral (C : Config) : Prop :=
  ¬ RotEquiv C (reflect C)

/-- [Element set] Membership of element `p` in the element set of `C`. -/
def HasElement (C : Config) (p : Nat) : Prop :=
  ∃ i : Fin C.length, (C.get i).p = p

/-- [Chemical formula] Multiplicity `n_p` of element `p` in configuration `C`. -/
def multiplicity (C : Config) (p : Nat) : Nat :=
  (C.filter (fun A => A.p == p)).length

end Config

/-- [Bond graph] Two distinct atom vertices `i` and `j` share a bond at point `x`. -/
def HasBondAt (C : Config) (i j : Fin C.length) (x : Phase) : Prop :=
  i ≠ j ∧ (C.get i).hasPoint x ∧ (C.get j).hasPoint x

/-- Adjacency in the bond graph: distinct vertices `i` and `j` share at least one point. -/
def BondAdj (C : Config) (i j : Fin C.length) : Prop :=
  ∃ x : Phase, HasBondAt C i j x

theorem bondAdj_irrefl (C : Config) (i : Fin C.length) : ¬ BondAdj C i i := by
  intro ⟨_, hne, _, _⟩
  exact hne rfl

theorem bondAdj_symm (C : Config) {i j : Fin C.length} (h : BondAdj C i j) : BondAdj C j i := by
  match h with
  | ⟨x, hne, hi, hj⟩ => exact ⟨x, Ne.symm hne, hj, hi⟩

/-- Reflexive-transitive closure of bond adjacency (walk in the bond graph). -/
inductive BondReachable (C : Config) : Fin C.length → Fin C.length → Prop where
  | refl (i : Fin C.length) : BondReachable C i i
  | step {i j k : Fin C.length} : BondAdj C i j → BondReachable C j k → BondReachable C i k

/-- The bond graph of `C` is connected if `C` is non-empty and any two vertices are connected by a walk. -/
def IsConnected (C : Config) : Prop :=
  C.length > 0 ∧ ∀ i j : Fin C.length, BondReachable C i j

/-- [Molecule] A connected configuration in which every point on every atom belongs to
exactly one other atom (so every point present lies on exactly two atoms). -/
structure IsMolecule (C : Config) : Prop where
  connected : IsConnected C
  paired : ∀ (i : Fin C.length) (x : Phase), (C.get i).hasPoint x →
    ∃ j : Fin C.length, i ≠ j ∧ (C.get j).hasPoint x ∧
      ∀ k : Fin C.length, (C.get k).hasPoint x → k = i ∨ k = j

/-- [In/out assignment] A 2-coloring of the vertices with opposite colors at every bond. -/
structure InOutAssignment (C : Config) where
  color : Fin C.length → Bool
  valid : ∀ i j : Fin C.length, BondAdj C i j → color i ≠ color j

/-- A configuration's bond graph is bipartite iff it admits an in/out assignment. -/
def IsBipartite (C : Config) : Prop :=
  Nonempty (InOutAssignment C)

/-- An in/out assignment exists iff the bond graph is bipartite. -/
theorem inOutAssignment_iff_isBipartite (C : Config) :
    (∃ _ : InOutAssignment C, True) ↔ IsBipartite C := by
  constructor
  · intro h
    match h with
    | ⟨a, _⟩ => exact ⟨a⟩
  · intro h
    match h with
    | ⟨a⟩ => exact ⟨a, trivial⟩

end CyclicAtoms
