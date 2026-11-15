import CyclicAtoms.Defs
import CyclicAtoms.FormulaPermutations

namespace CyclicAtoms.GeneralSynthesis

open UniversalSynthesis

def Elements (p q r : ℕ) (C : Config) : Prop :=
  ∀ a ∈ C, a.p = p ∨ a.p = q ∨ a.p = r

def configFormula (p q r : ℕ) (C : Config) : Formula :=
  ![(C.multiplicity p : ℤ), (C.multiplicity q : ℤ), (C.multiplicity r : ℤ)]

structure Molecule (p q r : ℕ) where
  config : Config
  molecule : IsMolecule config
  elements : Elements p q r config

def Molecule.formula {p q r : ℕ} (m : Molecule p q r) : Formula :=
  configFormula p q r m.config

theorem multiplicity_zero_of_other {p q r : ℕ} {C : Config}
    (hC : Elements p q r C) (e : ℕ) (hp : e ≠ p) (hq : e ≠ q) (hr : e ≠ r) :
    C.multiplicity e = 0 := by
  have hfilter : C.filter (fun a => a.p == e) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    have he := hC a ha
    have hne : a.p ≠ e := by omega
    simp [hne]
  simp [Config.multiplicity, hfilter]

/-- Every stock entry is an actual molecule from the original definition.
The replacement rule conserves all natural-number element counts. -/
inductive MolecularStep (p q r : ℕ) :
    Multiset (Molecule p q r) → Multiset (Molecule p q r) → Prop
  | replace (x y z w : Molecule p q r) (rest : Multiset (Molecule p q r))
      (conserved : ∀ e : ℕ,
        x.config.multiplicity e + y.config.multiplicity e =
          z.config.multiplicity e + w.config.multiplicity e) :
      MolecularStep p q r (x ::ₘ y ::ₘ rest) (z ::ₘ w ::ₘ rest)

inductive MolecularChain (p q r : ℕ) :
    Multiset (Molecule p q r) → Multiset (Molecule p q r) → Prop
  | refl (stock) : MolecularChain p q r stock stock
  | step {a b c} : MolecularStep p q r a b → MolecularChain p q r b c →
      MolecularChain p q r a c

def stockCount {p q r : ℕ} (stock : Multiset (Molecule p q r)) (e : ℕ) : ℕ :=
  (stock.map (fun m => m.config.multiplicity e)).sum

theorem MolecularStep.conserves {p q r : ℕ} {a b : Multiset (Molecule p q r)}
    (h : MolecularStep p q r a b) (e : ℕ) : stockCount a e = stockCount b e := by
  cases h with
  | replace x y z w rest conserved =>
    simpa only [stockCount, Multiset.map_cons, Multiset.sum_cons, ← Nat.add_assoc]
      using congrArg (· + stockCount rest e) (conserved e)

theorem MolecularChain.conserves {p q r : ℕ} {a b : Multiset (Molecule p q r)}
    (h : MolecularChain p q r a b) (e : ℕ) : stockCount a e = stockCount b e := by
  induction h with
  | refl => rfl
  | step hs _ ih => exact (hs.conserves e).trans ih

theorem MolecularChain.card_eq {p q r : ℕ} {a b : Multiset (Molecule p q r)}
    (h : MolecularChain p q r a b) : a.card = b.card := by
  induction h with
  | refl => rfl
  | step hs _ ih =>
    rw [← ih]
    cases hs
    simp

theorem formula_balance_conserves {p q r : ℕ} (x y z w : Molecule p q r)
    (h : x.formula + y.formula = z.formula + w.formula) (e : ℕ) :
    x.config.multiplicity e + y.config.multiplicity e =
      z.config.multiplicity e + w.config.multiplicity e := by
  by_cases hp : e = p
  · subst e
    have he := congrFun h 0
    simp only [Molecule.formula, configFormula, Pi.add_apply,
      Matrix.cons_val_zero] at he
    exact_mod_cast he
  by_cases hq : e = q
  · subst e
    have he := congrFun h 1
    simp only [Molecule.formula, configFormula, Pi.add_apply,
      Matrix.cons_val_one, Matrix.cons_val_zero] at he
    exact_mod_cast he
  by_cases hr : e = r
  · subst e
    have he := congrFun h 2
    simp only [Molecule.formula, configFormula, Pi.add_apply,
      Matrix.cons_val, Matrix.head_cons] at he
    exact_mod_cast he
  rw [multiplicity_zero_of_other x.elements e hp hq hr,
    multiplicity_zero_of_other y.elements e hp hq hr,
    multiplicity_zero_of_other z.elements e hp hq hr,
    multiplicity_zero_of_other w.elements e hp hq hr]

theorem formula_step_lifts {p q r : ℕ}
    (realize : Formula → Molecule p q r)
    (hr : ∀ f, Valid p q r f → (realize f).formula = f)
    {before after : Multiset Formula} (h : Step (Valid p q r) before after)
    (hb : ∀ f ∈ before, Valid p q r f) :
    MolecularStep p q r (before.map realize) (after.map realize) ∧
      (∀ f ∈ after, Valid p q r f) := by
  cases h with
  | replace x y z w rest hz hw balance =>
    have hx := hb x (by simp)
    have hy := hb y (by simp)
    have hbalance : (realize x).formula + (realize y).formula =
        (realize z).formula + (realize w).formula := by
      rw [hr x hx, hr y hy, hr z hz, hr w hw]
      exact balance
    constructor
    · simpa only [Multiset.map_cons] using MolecularStep.replace
        (realize x) (realize y) (realize z) (realize w) (rest.map realize)
        (formula_balance_conserves _ _ _ _ hbalance)
    · intro f hf
      simp only [Multiset.mem_cons] at hf
      rcases hf with rfl | rfl | hf
      · exact hz
      · exact hw
      · exact hb f (by simp [hf])

theorem formula_chain_lifts {p q r : ℕ}
    (realize : Formula → Molecule p q r)
    (hr : ∀ f, Valid p q r f → (realize f).formula = f)
    {initial final : Multiset Formula} (h : Chain (Valid p q r) initial final)
    (hi : ∀ f ∈ initial, Valid p q r f) :
    MolecularChain p q r (initial.map realize) (final.map realize) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih =>
    obtain ⟨hs', hb⟩ := formula_step_lifts realize hr hs hi
    exact .step hs' (ih hb)

theorem feed_valid (p q r : ℕ) (pair : Fin 3) :
    ∀ f ∈ feedPair p q r pair, Valid p q r f := by
  intro f hf
  left
  have hsubset : feedPair p q r pair ⊆
      [dimerP, dimerQ, dimerR, binaryPQ p q, binaryPR p r, binaryQR q r] := by
    fin_cases pair <;> simp [feedPair, List.subset_def]
  exact hsubset hf

/-- Lift the symbolic synthesis theorem once geometric classification and
realization have been proved. The original requested molecule is selected
whenever its formula appears, so the conclusion preserves its isomer. -/
theorem synthesis_of_classification_and_realization (p q r : ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (classify : ∀ m : Molecule p q r, Valid p q r m.formula)
    (realizable : ∀ f : Formula, Valid p q r f → ∃ m : Molecule p q r, m.formula = f)
    (target : Molecule p q r) (pair : Fin 3) :
    ∃ initial final : Multiset (Molecule p q r),
      (∀ m ∈ initial, m.formula ∈ feedPair p q r pair) ∧
      MolecularChain p q r initial final ∧ target ∈ final := by
  classical
  let realize : Formula → Molecule p q r := fun f =>
    if f = target.formula then target
    else if h : Valid p q r f then Classical.choose (realizable f h) else target
  have hformula : ∀ f, Valid p q r f → (realize f).formula = f := by
    intro f hf
    by_cases ht : f = target.formula
    · simp only [realize, if_pos ht]
      exact ht.symm
    · simp only [realize, if_neg ht, dif_pos hf]
      exact Classical.choose_spec (realizable f hf)
  obtain ⟨initial, final, hi, hc, ht⟩ := universal_synthesis_unordered p q r
    hp hq hr hpq hpr hqr pair target.formula (classify target)
  refine ⟨initial.map realize, final.map realize, ?_, ?_, ?_⟩
  · intro m hm
    obtain ⟨f, hf, rfl⟩ := Multiset.mem_map.mp hm
    rw [hformula f (feed_valid p q r pair f (hi f hf))]
    exact hi f hf
  · exact formula_chain_lifts realize hformula hc
      (fun f hf => feed_valid p q r pair f (hi f hf))
  · have heq : realize target.formula = target := by simp [realize]
    rw [← heq]
    exact Multiset.mem_map_of_mem realize ht

/-- info: 'CyclicAtoms.GeneralSynthesis.synthesis_of_classification_and_realization'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms synthesis_of_classification_and_realization

end CyclicAtoms.GeneralSynthesis
