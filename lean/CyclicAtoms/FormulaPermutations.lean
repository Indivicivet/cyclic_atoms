import CyclicAtoms.UniversalSynthesis

namespace CyclicAtoms.UniversalSynthesis

/-- Reorder element counts by the same permutation as the element names. -/
def permute (e : Equiv.Perm (Fin 3)) (f : Formula) : Formula := f ∘ e

theorem permute_add (e : Equiv.Perm (Fin 3)) (f g : Formula) :
    permute e (f + g) = permute e f + permute e g := rfl

theorem permute_swap_twice (i j : Fin 3) (f : Formula) :
    permute (Equiv.swap i j) (permute (Equiv.swap i j) f) = f := by
  ext k
  simp [permute]

@[simp] theorem permute_swap_first_third_vec (a b c : ℤ) :
    permute (Equiv.swap 0 2) ![a, b, c] = ![c, b, a] := by
  ext i
  fin_cases i <;> simp [permute, Equiv.swap_apply_def]

@[simp] theorem permute_swap_second_third_vec (a b c : ℤ) :
    permute (Equiv.swap 1 2) ![a, b, c] = ![a, c, b] := by
  ext i
  fin_cases i <;> simp [permute, Equiv.swap_apply_def]

theorem valid_swap_first_third {p q r : ℤ} {f : Formula} (h : Valid p q r f) :
    Valid r q p (permute (Equiv.swap 0 2) f) := by
  rcases h with h | ⟨a, b, c, ha, hap, hb, hbq, hc, hcr, hpos, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals left
    all_goals simp [dimerP, dimerQ, dimerR,
      binaryPQ, binaryPR, binaryQR]
  · have heq : permute (Equiv.swap 0 2) (parity p q r a b c) =
        parity r q p c b a := by
      ext i
      fin_cases i <;> simp [permute, Equiv.swap_apply_def, parity]
      all_goals ring
    refine Or.inr ⟨c, b, a, hc, hcr, hb, hbq, ha, hap, ?_, heq⟩
    intro i
    rw [← heq]
    exact hpos _

theorem valid_swap_second_third {p q r : ℤ} {f : Formula} (h : Valid p q r f) :
    Valid p r q (permute (Equiv.swap 1 2) f) := by
  rcases h with h | ⟨a, b, c, ha, hap, hb, hbq, hc, hcr, hpos, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals left
    all_goals simp [dimerP, dimerQ, dimerR,
      binaryPQ, binaryPR, binaryQR]
  · have heq : permute (Equiv.swap 1 2) (parity p q r a b c) =
        parity p r q a c b := by
      ext i
      fin_cases i <;> simp [permute, Equiv.swap_apply_def, parity]
      all_goals ring
    refine Or.inr ⟨a, c, b, ha, hap, hc, hcr, hb, hbq, ?_, heq⟩
    intro i
    rw [← heq]
    exact hpos _

private theorem feeds_swap_first_third (p q r : ℤ) (pair : Fin 3) :
    ∀ f ∈ feedPair r q p (![2, 1, 0] pair),
      permute (Equiv.swap 0 2) f ∈ feedPair p q r pair := by
  intro f hf
  fin_cases pair <;> simp [feedPair] at hf ⊢
  all_goals rcases hf with rfl | rfl
  all_goals simp [binaryPQ, binaryPR, binaryQR]

private theorem feeds_swap_second_third (p q r : ℤ) (pair : Fin 3) :
    ∀ f ∈ feedPair p r q (![0, 2, 1] pair),
      permute (Equiv.swap 1 2) f ∈ feedPair p q r pair := by
  intro f hf
  fin_cases pair <;> simp [feedPair] at hf ⊢
  all_goals rcases hf with rfl | rfl
  all_goals simp [binaryPQ, binaryPR, binaryQR]

/-- The formula synthesis theorem accepts the original ordering of any
three distinct dimensions at least two, including a 2 in any coordinate. -/
theorem every_valid_formula_unordered (p q r : ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (pair : Fin 3) (f : Formula) (hf : Valid p q r f) :
    Reachable (Valid p q r) (feedPair p q r pair) f := by
  by_cases hp3 : 3 ≤ p
  · by_cases hq3 : 3 ≤ q
    · exact every_valid_formula_from_any_pair p q r
        (by exact_mod_cast hp3) (by exact_mod_cast hq3) (by exact_mod_cast hr) pair f hf
    · have hr3 : 3 ≤ r := by omega
      have h := every_valid_formula_from_any_pair p r q
        (by exact_mod_cast hp3) (by exact_mod_cast hr3) (by exact_mod_cast hq)
        (![0, 2, 1] pair) (permute (Equiv.swap 1 2) f) (valid_swap_second_third hf)
      have h' := h.map (permute (Equiv.swap 1 2)) (permute_add _)
        (fun _ hg => valid_swap_second_third hg)
        (feeds' := feedPair p q r pair) (by
          intro g hg
          exact .feed (feeds_swap_second_third p q r pair g hg))
      simpa only [permute_swap_twice] using h'
  · have hq3 : 3 ≤ q := by omega
    have hr3 : 3 ≤ r := by omega
    have h := every_valid_formula_from_any_pair r q p
      (by exact_mod_cast hr3) (by exact_mod_cast hq3) (by exact_mod_cast hp)
      (![2, 1, 0] pair) (permute (Equiv.swap 0 2) f) (valid_swap_first_third hf)
    have h' := h.map (permute (Equiv.swap 0 2)) (permute_add _)
      (fun _ hg => valid_swap_first_third hg)
      (feeds' := feedPair p q r pair) (by
        intro g hg
        exact .feed (feeds_swap_first_third p q r pair g hg))
    simpa only [permute_swap_twice] using h'

theorem universal_synthesis_unordered (p q r : ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (pair : Fin 3) (f : Formula) (hf : Valid p q r f) :
    ∃ initial final : Multiset Formula,
      (∀ g ∈ initial, g ∈ feedPair p q r pair) ∧
      Chain (Valid p q r) initial final ∧ f ∈ final :=
  (every_valid_formula_unordered p q r hp hq hr hpq hpr hqr pair f hf).batch

/-- info: 'CyclicAtoms.UniversalSynthesis.universal_synthesis_unordered' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms universal_synthesis_unordered

end CyclicAtoms.UniversalSynthesis
