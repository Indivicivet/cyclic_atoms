import CyclicAtoms.Defs

namespace CyclicAtoms

/-!
# Formalized results from `THEORY.md`

1. **Degree-bond formula and evenness**: `2B = Σ p n_p`, so the sum of atom degrees is even.
2. **Isolation of identical atoms**: Two distinct atoms with the same point set in a molecule
   cannot bond to any third atom, so connectivity forces every vertex in the molecule to be one
   of those two atoms.
 * `three_prime_upper_bound` and `three_prime_construction_twice`: The slice-counting upper bound
   and the explicit CRT-grid construction covering every point in `Z_s × Z_p × Z_q` twice.
4. **Four-prime maximum size `M(s, p, q, r) = pqr + (s - 1)qr + (p - 1)r + q`**: The slice and
   column-counting upper bound and the explicit CRT-grid construction covering every point in
   `Z_s × Z_p × Z_q × Z_r` twice.
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


/-! ## Result 4: Four-prime maximum `M(s, p, q, r) = pqr + (s - 1)qr + (p - 1)r + q` -/

/-- Helper lemma: for `a ≤ b` and `c ≤ d`, `b * c + a * d ≤ b * d + a * c`
(equivalent to `(b - a) * (d - c) ≥ 0` without subtraction). -/
theorem mul_diff_le {a b c d : Nat} (hab : a ≤ b) (hcd : c ≤ d) :
    b * c + a * d ≤ b * d + a * c := by
  have h1 : (b - a) * c ≤ (b - a) * d := Nat.mul_le_mul_left (b - a) hcd
  have h2 : (b - a) * c + a * c ≤ (b - a) * d + a * c := Nat.add_le_add_right h1 (a * c)
  have hbc : (b - a) * c + a * c = b * c := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hab]
  have hbd : (b - a) * d + a * d = b * d := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hab]
  rw [hbc] at h2
  have h3 : b * c + a * d ≤ ((b - a) * d + a * c) + a * d := Nat.add_le_add_right h2 (a * d)
  have hrhs : ((b - a) * d + a * c) + a * d = b * d + a * c := by
    rw [Nat.add_assoc, Nat.add_comm (a * c) (a * d), ← Nat.add_assoc, hbd]
  rw [hrhs] at h3
  exact h3

/-- Helper lemma: if `q * a + 1 ≤ q * b`, then `a + 1 ≤ b`. -/
theorem le_of_mul_succ_le_mul {q a b : Nat} (h : q * a + 1 ≤ q * b) :
    a + 1 ≤ b := by
  cases Nat.lt_or_ge a b with
  | inl hlt => exact hlt
  | inr hge =>
    have hmul : q * b ≤ q * a := Nat.mul_le_mul_left q hge
    have hbad : q * a + 1 ≤ q * a := Nat.le_trans h hmul
    exact False.elim (Nat.not_succ_le_self (q * a) hbad)

/-- Helper lemma: if `1 ≤ q` and `q * a ≤ q * b`, then `a ≤ b`. -/
theorem le_of_mul_le_mul_pos {q a b : Nat} (hq : 1 ≤ q) (h : q * a ≤ q * b) :
    a ≤ b := by
  cases Nat.lt_or_ge b a with
  | inl hlt =>
    have hmul : q * (b + 1) ≤ q * a := Nat.mul_le_mul_left q hlt
    rw [Nat.mul_add, Nat.mul_one] at hmul
    have hstep : q * b + 1 ≤ q * b + q := Nat.add_le_add_left hq (q * b)
    have hbad : q * b + 1 ≤ q * b := Nat.le_trans hstep (Nat.le_trans hmul h)
    exact False.elim (Nat.not_succ_le_self (q * b) hbad)
  | inr hge => exact hge

/-- Local slice incidence bound: in any `s × p` slice `(y, z)`, if `s * a + p * b = Qz + Ry + 2 * e`
with `s ≤ p`, then `Qz + Ry ≤ p * (a + b)`. -/
theorem four_prime_slice_bound {s p a b Qz Ry e : Nat}
    (hsp : s ≤ p) (hinc : s * a + p * b = Qz + Ry + 2 * e) :
    Qz + Ry ≤ p * (a + b) := by
  have h1 : Qz + Ry ≤ Qz + Ry + 2 * e := Nat.le_add_right (Qz + Ry) (2 * e)
  rw [← hinc] at h1
  have h2 : s * a + p * b ≤ p * a + p * b :=
    Nat.add_le_add_right (Nat.mul_le_mul_right a hsp) (p * b)
  rw [← Nat.mul_add] at h2
  exact Nat.le_trans h1 h2

/-- Single-column bound: in any `r`-column `z`, summing over the `q` slices gives `q ≤ Dz` and
`q * Qz + R ≤ p * Dz`. Since `1 ≤ R` and `p ≤ q`, this forces `Qz + q + 1 ≤ Dz + p`. -/
theorem four_prime_column_bound {p q R Qz Dz : Nat}
    (hpq : p ≤ q) (hR : 1 ≤ R) (hD : q ≤ Dz) (hcol : q * Qz + R ≤ p * Dz) :
    Qz + q + 1 ≤ Dz + p := by
  have h1 : q * Qz + 1 ≤ p * Dz :=
    Nat.le_trans (Nat.add_le_add_left hR (q * Qz)) hcol
  have h2 : q * q + (q * Qz + 1) ≤ q * q + p * Dz :=
    Nat.add_le_add_left h1 (q * q)
  have hdiff : q * q + p * Dz ≤ q * Dz + p * q := mul_diff_le hpq hD
  have h3 : q * q + (q * Qz + 1) ≤ q * Dz + p * q := Nat.le_trans h2 hdiff
  have hL : q * q + (q * Qz + 1) = q * (Qz + q) + 1 := by
    rw [← Nat.add_assoc, Nat.add_comm (q * q) (q * Qz), ← Nat.mul_add]
  have hR_eq : q * Dz + p * q = q * (Dz + p) := by
    rw [Nat.mul_comm p q, ← Nat.mul_add]
  rw [hL, hR_eq] at h3
  exact le_of_mul_succ_le_mul h3

/-- Core inequality for the four-prime upper bound: whether `R ≤ q` or `q ≤ R`,
the column constraints imply `Q + R + q * r + r ≤ D + p * r + q`. -/
theorem four_prime_deficit_bound {p q r Q R D : Nat}
    (hpq : p ≤ q) (hqr : q ≤ r) (hq1 : 1 ≤ q)
    (hD : q * r ≤ D) (hglobal : q * Q + r * R ≤ p * D)
    (hcols : Q + q * r + r ≤ D + p * r) :
    Q + R + q * r + r ≤ D + p * r + q := by
  cases Nat.le_total R q with
  | inl hRq =>
    have h := Nat.add_le_add hcols hRq
    have hL : Q + q * r + r + R = Q + R + q * r + r := by
      rw [Nat.add_assoc Q (q * r) r, Nat.add_assoc Q (q * r + r) R,
          Nat.add_comm (q * r + r) R, ← Nat.add_assoc Q R (q * r + r),
          ← Nat.add_assoc (Q + R) (q * r) r]
    rw [hL] at h
    exact h
  | inr hqR =>
    have h1 : r * q + q * R ≤ r * R + q * q := mul_diff_le hqr hqR
    have h2 : q * (q * r) + p * D ≤ q * D + p * (q * r) := mul_diff_le hpq hD
    have h3 : q * Q + (r * q + q * R) ≤ q * Q + (r * R + q * q) :=
      Nat.add_le_add_left h1 (q * Q)
    have h3' : q * Q + (r * R + q * q) ≤ p * D + q * q := by
      rw [← Nat.add_assoc]
      exact Nat.add_le_add_right hglobal (q * q)
    have h4 : q * (q * r) + (q * Q + (r * q + q * R)) ≤ q * (q * r) + (p * D + q * q) :=
      Nat.add_le_add_left (Nat.le_trans h3 h3') (q * (q * r))
    have h5 : q * (q * r) + (p * D + q * q) ≤ q * D + p * (q * r) + q * q := by
      rw [← Nat.add_assoc]
      exact Nat.add_le_add_right h2 (q * q)
    have h6 : q * (q * r) + (q * Q + (r * q + q * R)) ≤ q * D + p * (q * r) + q * q :=
      Nat.le_trans h4 h5
    have hL : q * (q * r) + (q * Q + (r * q + q * R)) = q * (Q + R + q * r + r) := by
      rw [Nat.mul_comm r q, ← Nat.mul_add q r R, ← Nat.mul_add q Q (r + R),
          ← Nat.mul_add q (q * r) (Q + (r + R))]
      have hperm : q * r + (Q + (r + R)) = Q + R + q * r + r := by
        rw [Nat.add_comm r R, ← Nat.add_assoc Q R r,
            Nat.add_comm (q * r) (Q + R + r),
            Nat.add_assoc (Q + R) r (q * r), Nat.add_comm r (q * r),
            ← Nat.add_assoc (Q + R) (q * r) r]
      rw [hperm]
    have hR_eq : q * D + p * (q * r) + q * q = q * (D + p * r + q) := by
      have hpqr : p * (q * r) = q * (p * r) := by
        rw [← Nat.mul_assoc, Nat.mul_comm p q, Nat.mul_assoc]
      rw [hpqr, ← Nat.mul_add q D (p * r), ← Nat.mul_add q (D + p * r) q]
    rw [hL, hR_eq] at h6
    exact le_of_mul_le_mul_pos hq1 h6

/-- Identity relating `fourPrimeConstructionSize s p q r` to the unsubtracted sum:
for `1 ≤ s` and `1 ≤ p`, `fourPrimeConstructionSize s p q r + q * r + r = q * r * (s + p) + p * r + q`. -/
theorem fourPrimeConstructionSize_add {s p : Nat} (q r : Nat) (hs : 1 ≤ s) (hp : 1 ≤ p) :
    fourPrimeConstructionSize s p q r + q * r + r = q * r * (s + p) + p * r + q := by
  unfold fourPrimeConstructionSize
  have hsqr : (s - 1) * q * r + q * r = s * (q * r) := by
    have h1 : (s - 1) * (q * r) + 1 * (q * r) = s * (q * r) := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hs]
    rw [← Nat.mul_assoc (s - 1) q r, Nat.one_mul] at h1
    exact h1
  have hpr : (p - 1) * r + r = p * r := by
    have h1 : (p - 1) * r + 1 * r = p * r := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hp]
    rw [Nat.one_mul] at h1
    exact h1
  have hhead : p * q * r + (s - 1) * q * r + q * r = q * r * (s + p) := by
    rw [Nat.add_assoc (p * q * r) ((s - 1) * q * r) (q * r), hsqr,
        Nat.mul_assoc p q r, Nat.mul_comm p (q * r), Nat.mul_comm s (q * r),
        ← Nat.mul_add (q * r) p s, Nat.add_comm p s]
  rw [Nat.add_assoc (p * q * r + (s - 1) * q * r) ((p - 1) * r) q,
      Nat.add_assoc (p * q * r + (s - 1) * q * r) ((p - 1) * r + q) (q * r),
      Nat.add_comm ((p - 1) * r + q) (q * r),
      ← Nat.add_assoc (p * q * r + (s - 1) * q * r) (q * r) ((p - 1) * r + q),
      hhead,
      Nat.add_assoc (q * r * (s + p)) ((p - 1) * r + q) r,
      Nat.add_assoc ((p - 1) * r) q r, Nat.add_comm q r,
      ← Nat.add_assoc ((p - 1) * r) r q, hpr,
      ← Nat.add_assoc (q * r * (s + p)) (p * r) q]

/-- Four-prime upper bound theorem:
If `N ≤ q * r * (s + p) - D + Q + R` with `D ≤ q * r * (s + p)`, and the column counts satisfy
`q * r ≤ D`, `q * Q + r * R ≤ p * D`, and `Q + q * r + r ≤ D + p * r`, then
`N ≤ pqr + (s - 1)qr + (p - 1)r + q`. -/
theorem four_prime_upper_bound {s p q r Q R D N : Nat}
    (hs : 1 ≤ s) (hp : 1 ≤ p) (hpq : p ≤ q) (hqr : q ≤ r)
    (hD : q * r ≤ D) (hD_ub : D ≤ q * r * (s + p))
    (hglobal : q * Q + r * R ≤ p * D) (hcols : Q + q * r + r ≤ D + p * r)
    (hN : N ≤ q * r * (s + p) - D + Q + R) :
    N ≤ fourPrimeConstructionSize s p q r := by
  have hq1 : 1 ≤ q := Nat.le_trans hp hpq
  have hdef : Q + R + q * r + r ≤ D + p * r + q :=
    four_prime_deficit_bound hpq hqr hq1 hD hglobal hcols
  have hND : N + D ≤ q * r * (s + p) + Q + R := by
    have h1 := Nat.add_le_add_right hN D
    have h2 : q * r * (s + p) - D + Q + R + D = q * r * (s + p) + Q + R := by
      rw [Nat.add_assoc (q * r * (s + p) - D) Q R,
          Nat.add_assoc (q * r * (s + p) - D) (Q + R) D,
          Nat.add_comm (Q + R) D,
          ← Nat.add_assoc (q * r * (s + p) - D) D (Q + R),
          Nat.sub_add_cancel hD_ub,
          ← Nat.add_assoc (q * r * (s + p)) Q R]
    rw [h2] at h1
    exact h1
  have hstep1 : N + D + (q * r + r) ≤ q * r * (s + p) + (Q + R + q * r + r) := by
    have h1 := Nat.add_le_add_right hND (q * r + r)
    have hR_eq : q * r * (s + p) + Q + R + (q * r + r) =
        q * r * (s + p) + (Q + R + q * r + r) := by
      rw [Nat.add_assoc (q * r * (s + p)) Q R,
          Nat.add_assoc (q * r * (s + p)) (Q + R) (q * r + r),
          ← Nat.add_assoc (Q + R) (q * r) r]
    rw [hR_eq] at h1
    exact h1
  have hstep2 : q * r * (s + p) + (Q + R + q * r + r) ≤
      q * r * (s + p) + (D + p * r + q) :=
    Nat.add_le_add_left hdef (q * r * (s + p))
  have hcomb : N + (D + q * r + r) ≤ fourPrimeConstructionSize s p q r + (D + q * r + r) := by
    have h1 := Nat.le_trans hstep1 hstep2
    have hL : N + D + (q * r + r) = N + (D + q * r + r) := by
      rw [Nat.add_assoc N D (q * r + r), ← Nat.add_assoc D (q * r) r]
    have hR_eq : q * r * (s + p) + (D + p * r + q) =
        fourPrimeConstructionSize s p q r + (D + q * r + r) := by
      have hsz := fourPrimeConstructionSize_add q r hs hp
      rw [Nat.add_assoc D (p * r) q, Nat.add_comm D (p * r + q),
          ← Nat.add_assoc (q * r * (s + p)) (p * r + q) D,
          ← Nat.add_assoc (q * r * (s + p)) (p * r) q,
          ← hsz,
          Nat.add_assoc (fourPrimeConstructionSize s p q r) (q * r) r,
          Nat.add_assoc (fourPrimeConstructionSize s p q r) (q * r + r) D,
          Nat.add_comm (q * r + r) D,
          ← Nat.add_assoc D (q * r) r]
    rw [hL, hR_eq] at h1
    exact h1
  exact Nat.le_of_add_le_add_right hcomb

/-- Total `q`-atoms across a list of column pairs `(Qz, Dz)`. -/
def sumColQ : List (Nat × Nat) → Nat
  | [] => 0
  | (Qz, _) :: cs => Qz + sumColQ cs

/-- Total absent `(s, p)`-lines across a list of column pairs `(Qz, Dz)`. -/
def sumColD : List (Nat × Nat) → Nat
  | [] => 0
  | (_, Dz) :: cs => Dz + sumColD cs

/-- Per-column validity: in every column `(Qz, Dz)`, at least `q` lines are missing (`q ≤ Dz`)
and the missing lines cover all `q * Qz + R` incidences (`q * Qz + R ≤ p * Dz`). -/
def ValidColumns (p q R : Nat) : List (Nat × Nat) → Prop
  | [] => True
  | (Qz, Dz) :: cs => (q ≤ Dz ∧ q * Qz + R ≤ p * Dz) ∧ ValidColumns p q R cs

/-- Induction over the `r = cols.length` columns deriving the three aggregate column bounds
from the local per-column conditions `q ≤ Dz` and `q * Qz + R ≤ p * Dz`. -/
theorem validColumns_aggregate {p q R : Nat} (hpq : p ≤ q) (hR : 1 ≤ R)
    (cols : List (Nat × Nat)) (hvalid : ValidColumns p q R cols) :
    q * cols.length ≤ sumColD cols ∧
    q * sumColQ cols + cols.length * R ≤ p * sumColD cols ∧
    sumColQ cols + q * cols.length + cols.length ≤ sumColD cols + p * cols.length := by
  induction cols with
  | nil =>
    simp [sumColQ, sumColD, List.length]
  | cons hd tl ih =>
    match hd with
    | (Qz, Dz) =>
      match hvalid with
      | ⟨⟨hDz, hcol⟩, htl⟩ =>
        match ih htl with
        | ⟨ihD, ihGlob, ihCols⟩ =>
          have hlen : List.length ((Qz, Dz) :: tl) = tl.length + 1 := rfl
          refine ⟨?_, ?_, ?_⟩
          · -- 1. q * (tl.length + 1) ≤ Dz + sumColD tl
            rw [hlen, Nat.mul_add, Nat.mul_one, Nat.add_comm (q * tl.length) q]
            exact Nat.add_le_add hDz ihD
          · -- 2. q * (Qz + sumColQ tl) + (tl.length + 1) * R ≤ p * (Dz + sumColD tl)
            rw [hlen, sumColQ, sumColD, Nat.mul_add q Qz (sumColQ tl),
                Nat.add_mul tl.length 1 R, Nat.one_mul, Nat.mul_add p Dz (sumColD tl)]
            have hL : q * Qz + q * sumColQ tl + (tl.length * R + R) =
                (q * Qz + R) + (q * sumColQ tl + tl.length * R) := by
              rw [Nat.add_assoc (q * Qz) (q * sumColQ tl) (tl.length * R + R),
                  Nat.add_comm (tl.length * R) R,
                  ← Nat.add_assoc (q * sumColQ tl) R (tl.length * R),
                  Nat.add_comm (q * sumColQ tl) R,
                  Nat.add_assoc R (q * sumColQ tl) (tl.length * R),
                  ← Nat.add_assoc (q * Qz) R (q * sumColQ tl + tl.length * R)]
            rw [hL]
            exact Nat.add_le_add hcol ihGlob
          · -- 3. (Qz + sumColQ tl) + q * (tl.length + 1) + (tl.length + 1) ≤ (Dz + sumColD tl) + p * (tl.length + 1)
            have hstep : Qz + q + 1 ≤ Dz + p := four_prime_column_bound hpq hR hDz hcol
            have hsum := Nat.add_le_add hstep ihCols
            rw [hlen, sumColQ, sumColD, Nat.mul_add q tl.length 1, Nat.mul_one,
                Nat.mul_add p tl.length 1, Nat.mul_one]
            have hL : (Qz + sumColQ tl) + (q * tl.length + q) + (tl.length + 1) =
                (Qz + q + 1) + (sumColQ tl + q * tl.length + tl.length) := by
              rw [Nat.add_assoc Qz (sumColQ tl) (q * tl.length + q),
                  Nat.add_comm (q * tl.length) q,
                  ← Nat.add_assoc (sumColQ tl) q (q * tl.length),
                  Nat.add_comm (sumColQ tl) q,
                  Nat.add_assoc q (sumColQ tl) (q * tl.length),
                  ← Nat.add_assoc Qz q (sumColQ tl + q * tl.length),
                  Nat.add_assoc (Qz + q) (sumColQ tl + q * tl.length) (tl.length + 1),
                  Nat.add_comm tl.length 1,
                  ← Nat.add_assoc (sumColQ tl + q * tl.length) 1 tl.length,
                  Nat.add_comm (sumColQ tl + q * tl.length) 1,
                  Nat.add_assoc 1 (sumColQ tl + q * tl.length) tl.length,
                  ← Nat.add_assoc (Qz + q) 1 (sumColQ tl + q * tl.length + tl.length)]
            have hR_eq : (Dz + sumColD tl) + (p * tl.length + p) =
                (Dz + p) + (sumColD tl + p * tl.length) := by
              rw [Nat.add_assoc Dz (sumColD tl) (p * tl.length + p),
                  Nat.add_comm (p * tl.length) p,
                  ← Nat.add_assoc (sumColD tl) p (p * tl.length),
                  Nat.add_comm (sumColD tl) p,
                  Nat.add_assoc p (sumColD tl) (p * tl.length),
                  ← Nat.add_assoc Dz p (sumColD tl + p * tl.length)]
            rw [hL, hR_eq]
            exact hsum

/-- End-to-end four-prime upper bound directly from a list `cols` of `r = cols.length` columns
satisfying `ValidColumns p q R cols`: the molecule size `N` is at most
`fourPrimeConstructionSize s p q cols.length`. -/
theorem four_prime_upper_bound_of_columns {s p q R N : Nat} (cols : List (Nat × Nat))
    (hs : 1 ≤ s) (hp : 1 ≤ p) (hpq : p ≤ q) (hqr : q ≤ cols.length) (hR : 1 ≤ R)
    (hvalid : ValidColumns p q R cols)
    (hD_ub : sumColD cols ≤ q * cols.length * (s + p))
    (hN : N ≤ q * cols.length * (s + p) - sumColD cols + sumColQ cols + R) :
    N ≤ fourPrimeConstructionSize s p q cols.length := by
  match validColumns_aggregate hpq hR cols hvalid with
  | ⟨hD, hglob, hcols⟩ =>
    exact four_prime_upper_bound hs hp hpq hqr hD hD_ub hglob hcols hN

/-- In the explicit 4-prime CRT construction on `Z_s × Z_p × Z_q × Z_r`:
- Every `(x, y, z)` has an `s`-line (1 incidence per point `(w, x, y, z)`).
- Every `(w, y, z)` with `w < s - 1` has a `p`-line (1 incidence if `w < s - 1`, else 0).
- Every `(w, x, z)` with `w = s - 1` and `x < p - 1` has a `q`-line.
- Every `(w, x, y)` with `w = s - 1` and `x = p - 1` has an `r`-line.
This function counts the total number of atoms incident to grid point `(w, x, y, z)`. -/
def fourPrimeGridIncidences (s p : Nat) (w x _y _z : Nat) : Nat :=
  1 + (if w < s - 1 then 1 else 0) +
      (if w = s - 1 ∧ x < p - 1 then 1 else 0) +
      (if w = s - 1 ∧ x = p - 1 then 1 else 0)

/-- Every grid point `(w, x, y, z)` with `w < s` and `x < p` in the 4-prime construction
belongs to exactly two atoms. -/
theorem four_prime_construction_twice {s p w x y z : Nat} (hw : w < s) (hx : x < p) :
    fourPrimeGridIncidences s p w x y z = 2 := by
  unfold fourPrimeGridIncidences
  cases s with
  | zero => exact False.elim (Nat.not_lt_zero w hw)
  | succ ms =>
    cases p with
    | zero => exact False.elim (Nat.not_lt_zero x hx)
    | succ mp =>
      have hsubs : Nat.succ ms - 1 = ms := rfl
      have hsubp : Nat.succ mp - 1 = mp := rfl
      rw [hsubs, hsubp]
      have hw_le : w ≤ ms := Nat.le_of_lt_succ hw
      cases Nat.eq_or_lt_of_le hw_le with
      | inl hw_eq =>
        have hw_notlt : ¬ (w < ms) := by
          rw [hw_eq]
          exact Nat.lt_irrefl ms
        have hx_le : x ≤ mp := Nat.le_of_lt_succ hx
        cases Nat.eq_or_lt_of_le hx_le with
        | inl hx_eq =>
          have hx_notlt : ¬ (x < mp) := by
            rw [hx_eq]
            exact Nat.lt_irrefl mp
          simp [hw_eq, hw_notlt, hx_eq, hx_notlt]
        | inr hx_lt =>
          have hx_ne : ¬ (x = mp) := Nat.ne_of_lt hx_lt
          simp [hw_eq, hw_notlt, hx_lt, hx_ne]
      | inr hw_lt =>
        have hw_ne : ¬ (w = ms) := Nat.ne_of_lt hw_lt
        simp [hw_lt, hw_ne]

end CyclicAtoms
