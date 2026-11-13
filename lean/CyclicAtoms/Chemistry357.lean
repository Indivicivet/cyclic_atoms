import CyclicAtoms.Chemistry357Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CyclicAtoms.Chemistry

theorem catalog_length357 : formulas357.length = 86 := by decide

def witnessChecks357 (i : Fin 86) : Bool :=
  moleculeOnGrid (gridWitnesses357.getD i.val []) &&
    decide (gridFormula (gridWitnesses357.getD i.val []) = formula357 i)

theorem witness_checks357 : allFinCheck 86 witnessChecks357 = true := by native_decide

/-- Every catalog entry has a paired, connected 105-site grid witness. -/
theorem catalog_witnesses357 (i : Fin 86) :
    moleculeOnGrid (gridWitnesses357.getD i.val []) = true ∧
    gridFormula (gridWitnesses357.getD i.val []) = formula357 i := by
  have h := allFinCheck_sound 86 witnessChecks357 witness_checks357 i
  exact ⟨and_left_true _ _ h, of_decide_eq_true (and_right_true _ _ h)⟩

def batchChecks357 (p : Fin 3) (i : Fin 86) : Bool :=
  checkPlan formulas357 reactionTable357 (feedPair357 p) (formula357 i)
    (certificate357 p i)

theorem certificate_checks357 :
    allFinCheck 3 (fun p => allFinCheck 86 (batchChecks357 p)) = true := by native_decide

/-- Independently check every step, all feed supplies, and all target copies. -/
theorem certificates_valid357 (p : Fin 3) (i : Fin 86) :
    checkPlan formulas357 reactionTable357 (feedPair357 p) (formula357 i)
      (certificate357 p i) = true :=
  allFinCheck_sound 86 (batchChecks357 p)
    (allFinCheck_sound 3 _ certificate_checks357 p) i

theorem reactions_are_two_to_two357 :
    reactionTable357.all (fun r => decide
      (r.inputs.length = 2 ∧ r.outputs.length = 2)) = true := by decide

theorem every_catalog_formula_synthesizable357 (p : Fin 3) (i : Fin 86) :
    Synthesizable formulas357 reactionTable357 (feedPair357 p) (formula357 i) :=
  ⟨certificate357 p i, certificates_valid357 p i⟩

/-- The count formulas cover every positive three-element parity profile. -/
theorem parity_formula_in_catalog357 :
    ∀ a : Fin 2, ∀ b : Fin 6, ∀ c : Fin 8,
      threeElements (parityFormula a b c) →
      ∃ i : Fin 86, formula357 i = parityFormula a b c := by native_decide

theorem every_parity_formula_synthesizable357 (p : Fin 3)
    (a : Fin 2) (b : Fin 6) (c : Fin 8)
    (h : threeElements (parityFormula a b c)) :
    Synthesizable formulas357 reactionTable357 (feedPair357 p)
      (parityFormula a b c) := by
  match parity_formula_in_catalog357 a b c h with
  | ⟨i, hi⟩ =>
    rw [← hi]
    exact every_catalog_formula_synthesizable357 p i

/-- Every nonempty connected parity formula (1-, 2-, or 3-element) is in the catalog. -/
theorem connected_parity_formula_in_catalog357 :
    ∀ a : Fin 2, ∀ b : Fin 6, ∀ c : Fin 8,
      (0 < (parityFormula a b c).n3 ∨ 0 < (parityFormula a b c).n5 ∨
        0 < (parityFormula a b c).n7) →
      ((parityFormula a b c).n3 = 0 →
        (parityFormula a b c).n5 ≤ 7 ∧ (parityFormula a b c).n7 ≤ 5) →
      ((parityFormula a b c).n5 = 0 →
        (parityFormula a b c).n3 ≤ 7 ∧ (parityFormula a b c).n7 ≤ 3) →
      ((parityFormula a b c).n7 = 0 →
        (parityFormula a b c).n3 ≤ 5 ∧ (parityFormula a b c).n5 ≤ 3) →
      ∃ i : Fin 86, formula357 i = parityFormula a b c := by native_decide

theorem connected_parity_formula_synthesizable357 (p : Fin 3)
    (a : Fin 2) (b : Fin 6) (c : Fin 8)
    (hne : 0 < (parityFormula a b c).n3 ∨ 0 < (parityFormula a b c).n5 ∨
      0 < (parityFormula a b c).n7)
    (hz3 : (parityFormula a b c).n3 = 0 →
      (parityFormula a b c).n5 ≤ 7 ∧ (parityFormula a b c).n7 ≤ 5)
    (hz5 : (parityFormula a b c).n5 = 0 →
      (parityFormula a b c).n3 ≤ 7 ∧ (parityFormula a b c).n7 ≤ 3)
    (hz7 : (parityFormula a b c).n7 = 0 →
      (parityFormula a b c).n3 ≤ 5 ∧ (parityFormula a b c).n5 ≤ 3) :
    Synthesizable formulas357 reactionTable357 (feedPair357 p)
      (parityFormula a b c) := by
  match connected_parity_formula_in_catalog357 a b c hne hz3 hz5 hz7 with
  | ⟨i, hi⟩ =>
    rw [← hi]
    exact every_catalog_formula_synthesizable357 p i

#print axioms every_parity_formula_synthesizable357
#print axioms parity_factorization

end CyclicAtoms.Chemistry
