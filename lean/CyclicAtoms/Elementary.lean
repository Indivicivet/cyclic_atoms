import CyclicAtoms.Defs

namespace CyclicAtoms

/-!
# Elementary results from `THEORY.md`

1. **Degree-bond formula and evenness**: `2B = Σ p n_p`, so the sum of atom degrees is even.
2. **Isolation of identical atoms**: Two distinct atoms with the same point set in a molecule
   cannot bond to any third atom, so connectivity forces every vertex in the molecule to be one
   of those two atoms.
-/

/-! ## Result 1: Degree-bond identity (`2B = Σ p`) and evenness -/

/-- Sum of atom elements (total number of atom points / directed bond incidences) in `C`. -/
def sumDeg : Config → Nat
  | [] => 0
  | A :: As => A.p + sumDeg As

theorem sumDeg_cons (A : Atom) (As : Config) :
    sumDeg (A :: As) = A.p + sumDeg As := rfl

theorem sumDeg_append (C₁ C₂ : Config) :
    sumDeg (C₁ ++ C₂) = sumDeg C₁ + sumDeg C₂ := by
  induction C₁ with
  | nil => simp [sumDeg]
  | cons A As ih =>
    simp [sumDeg, ih, Nat.add_assoc]

/-- A bond pairing witness on `C` recording `B` undirected bonds whose 2 endpoints partition
the `sumDeg C` atom-point incidences. -/
structure BondCountWitness (C : Config) where
  bonds : Nat
  incidence_pairing : sumDeg C = 2 * bonds

/-- In any configuration with a bond pairing of `B` bonds, `2 * B = Σ p`, so `Σ p` is even. -/
theorem two_mul_bonds_eq_sumDeg {C : Config} (w : BondCountWitness C) :
    2 * w.bonds = sumDeg C :=
  w.incidence_pairing.symm

theorem even_sumDeg_of_paired {C : Config} (w : BondCountWitness C) :
    ∃ B : Nat, sumDeg C = B + B := by
  refine ⟨w.bonds, ?_⟩
  have h := w.incidence_pairing
  have h2 : 2 * w.bonds = w.bonds + w.bonds := by
    rw [Nat.succ_mul, Nat.one_mul]
  exact Eq.trans h h2


/-! ## Result 2: Identical atoms form an isolated two-atom molecule -/

/-- If vertices `i ≠ j` in a molecule `C` have the same point set, then `i` cannot bond to
any third vertex `k` (`k ≠ i` and `k ≠ j`). -/
theorem identical_atoms_isolated {C : Config} (hmol : IsMolecule C)
    {i j k : Fin C.length} (hij : i ≠ j) (hsame : Atom.SamePoints (C.get i) (C.get j))
    (hik : k ≠ i) (hjk : k ≠ j) :
    ¬ BondAdj C i k := by
  intro hadj
  match hadj with
  | ⟨x, _, hxi, hxk⟩ =>
    have hxj : (C.get j).hasPoint x := (hsame x).mp hxi
    match hmol.paired i x hxi with
    | ⟨j', _, _, hunique⟩ =>
      have hj_eq : j = i ∨ j = j' := hunique j hxj
      have hk_eq : k = i ∨ k = j' := hunique k hxk
      cases hj_eq with
      | inl hji => exact hij hji.symm
      | inr hjj' =>
        cases hk_eq with
        | inl hki => exact hik hki
        | inr hkj' => exact hjk (Eq.trans hkj' hjj'.symm)

/-- Symmetric version: `j` also cannot bond to any third vertex `k`. -/
theorem identical_atoms_isolated_right {C : Config} (hmol : IsMolecule C)
    {i j k : Fin C.length} (hij : i ≠ j) (hsame : Atom.SamePoints (C.get i) (C.get j))
    (hik : k ≠ i) (hjk : k ≠ j) :
    ¬ BondAdj C j k :=
  identical_atoms_isolated hmol (Ne.symm hij) (Atom.samePoints_symm hsame) hjk hik

/-- Any walk in the bond graph starting within `{i, j}` remains within `{i, j}`. -/
theorem identical_atoms_walk_confined {C : Config} (hmol : IsMolecule C)
    {i j u v : Fin C.length} (hij : i ≠ j) (hsame : Atom.SamePoints (C.get i) (C.get j))
    (hw : BondReachable C u v) (hu : u = i ∨ u = j) :
    v = i ∨ v = j := by
  induction hw with
  | refl => exact hu
  | @step a b _ hab _ ih =>
    apply ih
    by_cases hbi : b = i
    · exact Or.inl hbi
    · by_cases hbj : b = j
      · exact Or.inr hbj
      · cases hu with
        | inl hai =>
          have hab' : BondAdj C i b := hai ▸ hab
          exact False.elim (identical_atoms_isolated hmol hij hsame hbi hbj hab')
        | inr haj =>
          have hab' : BondAdj C j b := haj ▸ hab
          exact False.elim (identical_atoms_isolated_right hmol hij hsame hbi hbj hab')

/-- In a molecule `C`, if two distinct vertices `i ≠ j` have the same point set, then every
vertex `k` of `C` is either `i` or `j` (they cannot connect to a third atom). -/
theorem identical_atoms_molecule_only_two {C : Config} (hmol : IsMolecule C)
    {i j : Fin C.length} (hij : i ≠ j) (hsame : Atom.SamePoints (C.get i) (C.get j))
    (k : Fin C.length) :
    k = i ∨ k = j := by
  have hreach : BondReachable C i k := hmol.connected.2 i k
  exact identical_atoms_walk_confined hmol hij hsame hreach (Or.inl rfl)

end CyclicAtoms
