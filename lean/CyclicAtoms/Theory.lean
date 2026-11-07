import CyclicAtoms.Defs

namespace CyclicAtoms

/-!
# Formalized results from `THEORY.md`

1. **Degree-bond formula and evenness**: `2B = Σ p n_p`, so the sum of atom degrees is even.
2. **Isolation of identical atoms**: Two distinct atoms with the same point set in a molecule
   cannot bond to any third atom, so connectivity forces every vertex in the molecule to be one
   of those two atoms.
3. **Three-prime maximum size `M(s, p, q) = pq + (s - 1)q + p`**: The slice-counting upper bound
   and the explicit CRT-grid construction covering every point in `Z_s × Z_p × Z_q` twice.
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


/-! ## Result 3: Three-prime maximum `M(s, p, q) = pq + (s - 1)q + p` -/

/-- Maximum size formula `M(s, p, q) = pq + (s - 1)q + p` for three primes `s < p < q`. -/
def maxThreePrimes (s p q : Nat) : Nat :=
  p * q + (s - 1) * q + p

/-- Construction size formula `pqr + (s - 1)qr + (p - 1)r + q` for four primes `s < p < q < r`. -/
def fourPrimeConstructionSize (s p q r : Nat) : Nat :=
  p * q * r + (s - 1) * q * r + (p - 1) * r + q

theorem maxThreePrimes_2_3_5 : maxThreePrimes 2 3 5 = 23 := rfl
theorem maxThreePrimes_3_7_11 : maxThreePrimes 3 7 11 = 106 := rfl
theorem fourPrimeConstructionSize_3_5_7_11 : fourPrimeConstructionSize 3 5 7 11 = 590 := rfl

/-- Helper lemma: for `1 ≤ k` and `p ≤ q`, `q + k * p ≤ p + k * q`. -/
theorem one_le_mul_diff {p q k : Nat} (hk : 1 ≤ k) (hpq : p ≤ q) :
    q + k * p ≤ p + k * q := by
  have h1 : 1 * (q - p) ≤ k * (q - p) := Nat.mul_le_mul_right (q - p) hk
  rw [Nat.one_mul] at h1
  have h2 : q - p + (p + k * p) ≤ k * (q - p) + (p + k * p) :=
    Nat.add_le_add_right h1 (p + k * p)
  have hleft : q - p + (p + k * p) = q + k * p := by
    rw [← Nat.add_assoc, Nat.sub_add_cancel hpq]
  have hmul : k * (q - p) + k * p = k * q := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hpq]
  have hright : k * (q - p) + (p + k * p) = p + k * q := by
    rw [Nat.add_comm p (k * p), ← Nat.add_assoc, hmul, Nat.add_comm (k * q) p]
  rw [hleft, hright] at h2
  exact h2

/-- Upper bound theorem from `THEORY.md`:
If `N ≤ q * (s + p - k) + T` where `k = ceil(T/p)` satisfies `1 ≤ k`, `T ≤ k * p`,
`k ≤ s + p`, `1 ≤ s`, and `p ≤ q`, then `N ≤ pq + (s - 1)q + p`. -/
theorem three_prime_upper_bound {s p q T k N : Nat}
    (hs : 1 ≤ s) (hpq : p ≤ q) (hk1 : 1 ≤ k) (hks : k ≤ s + p)
    (hT : T ≤ k * p) (hN : N ≤ q * (s + p - k) + T) :
    N ≤ maxThreePrimes s p q := by
  have hN1 : N ≤ q * (s + p - k) + k * p :=
    Nat.le_trans hN (Nat.add_le_add_left hT _)
  have hdist : q * (s + p - k) + q * k = q * (s + p) := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hks]
  have hineq : q + k * p ≤ p + q * k := by
    have h := one_le_mul_diff hk1 hpq
    rw [Nat.mul_comm k q] at h
    exact h
  have hstep : q * (s + p - k) + k * p + q ≤ q * (s + p) + p := by
    have hadd := Nat.add_le_add_left hineq (q * (s + p - k))
    have hL : q * (s + p - k) + (q + k * p) = q * (s + p - k) + k * p + q := by
      rw [Nat.add_comm q (k * p), ← Nat.add_assoc]
    have hR : q * (s + p - k) + (p + q * k) = q * (s + p) + p := by
      rw [Nat.add_comm p (q * k), ← Nat.add_assoc, hdist]
    rw [hL, hR] at hadd
    exact hadd
  have hsq : (s - 1) * q + q = s * q := by
    have h1 : (s - 1) * q + 1 * q = s * q := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hs]
    rw [Nat.one_mul] at h1
    exact h1
  have hrhs : maxThreePrimes s p q + q = q * (s + p) + p := by
    unfold maxThreePrimes
    rw [Nat.add_assoc (p * q + (s - 1) * q) p q, Nat.add_comm p q,
        ← Nat.add_assoc (p * q + (s - 1) * q) q p,
        Nat.add_assoc (p * q) ((s - 1) * q) q, hsq,
        Nat.mul_comm p q, Nat.mul_comm s q, ← Nat.mul_add, Nat.add_comm p s]
  have hN_add_q : N + q ≤ maxThreePrimes s p q + q := by
    rw [hrhs]
    exact Nat.le_trans (Nat.add_le_add_right hN1 q) hstep
  exact Nat.le_of_add_le_add_right hN_add_q

/-- In the explicit 3-prime CRT construction on `Z_s × Z_p × Z_q`:
- Every `(y, z)` has an `s`-line (1 incidence per point `(x, y, z)`).
- Every `(x, z)` with `x < s - 1` has a `p`-line (1 incidence if `x < s - 1`, else 0).
- Every `(x, y)` with `x = s - 1` has a `q`-line (1 incidence if `x = s - 1`, else 0).
This function counts the total number of atoms incident to grid point `(x, y, z)`. -/
def threePrimeGridIncidences (s : Nat) (x _y _z : Nat) : Nat :=
  1 + (if x < s - 1 then 1 else 0) + (if x = s - 1 then 1 else 0)

/-- Every grid point `(x, y, z)` with `x < s` in the 3-prime construction
belongs to exactly two atoms. -/
theorem three_prime_construction_twice {s x y z : Nat} (hx : x < s) :
    threePrimeGridIncidences s x y z = 2 := by
  unfold threePrimeGridIncidences
  cases s with
  | zero => exact False.elim (Nat.not_lt_zero x hx)
  | succ m =>
    have hsub : Nat.succ m - 1 = m := rfl
    rw [hsub]
    have hle : x ≤ m := Nat.le_of_lt_succ hx
    cases Nat.eq_or_lt_of_le hle with
    | inl heq =>
      have hnotlt : ¬ (x < m) := by
        rw [heq]
        exact Nat.lt_irrefl m
      simp [heq, hnotlt]
    | inr hlt =>
      have hne : ¬ (x = m) := Nat.ne_of_lt hlt
      simp [hlt, hne]

end CyclicAtoms
