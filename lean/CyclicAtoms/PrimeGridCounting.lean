import CyclicAtoms.PrimeGrid
import CyclicAtoms.Chemistry

namespace CyclicAtoms.PrimeGrid

attribute [local instance] Classical.propDecidable

theorem counts_p {p q r : ℕ} (S : Finset (Line p q r)) :
    counts S 0 = ((S.filter
      (fun l => match l with | .pLine _ _ => True | _ => False)).card : ℤ) := rfl

theorem counts_q {p q r : ℕ} (S : Finset (Line p q r)) :
    counts S 1 = ((S.filter
      (fun l => match l with | .qLine _ _ => True | _ => False)).card : ℤ) := rfl

theorem counts_r {p q r : ℕ} (S : Finset (Line p q r)) :
    counts S 2 = ((S.filter
      (fun l => match l with | .rLine _ _ => True | _ => False)).card : ℤ) := rfl

theorem weight_le {n : ℕ} (f : Fin n → Bool) : weight f ≤ n := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_fin n)

private theorem xor_card {m n : ℕ} (f : Fin m → Bool) (g : Fin n → Bool) :
    ((Finset.univ.filter fun xy : Fin m × Fin n => f xy.1 ≠ g xy.2).card : ℤ) =
      (weight f : ℤ) * (n - (weight g : ℤ)) + (m - (weight f : ℤ)) * weight g := by
  classical
  have hset : (Finset.univ.filter fun xy : Fin m × Fin n => f xy.1 ≠ g xy.2) =
      (Finset.univ ×ˢ Finset.univ).filter
        (fun xy : Fin m × Fin n => (f xy.1 = true) = (g xy.2 = false)) := by
    ext ⟨x, y⟩
    cases hf : f x <;> cases hg : g y <;> simp [hf, hg]
  rw [hset]
  have hcard := Finset.filter_product_card (Finset.univ : Finset (Fin m))
    (Finset.univ : Finset (Fin n)) (fun x => f x = true) (fun y => g y = false)
  rw [hcard]
  have hf := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Finset.univ) (fun x : Fin m => f x = true)
  have hg := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Finset.univ) (fun y : Fin n => g y = false)
  simp only [Finset.card_univ, Fintype.card_fin] at hf hg
  have hf' : ((Finset.univ.filter fun x : Fin m => f x = true).card : ℤ) +
      (Finset.univ.filter fun x : Fin m => ¬f x = true).card = m := by exact_mod_cast hf
  have hg' : ((Finset.univ.filter fun y : Fin n => g y = false).card : ℤ) +
      (Finset.univ.filter fun y : Fin n => ¬g y = false).card = n := by exact_mod_cast hg
  have hnot : (Finset.univ.filter fun y : Fin n => ¬g y = false) =
      Finset.univ.filter (fun y => g y = true) := by ext y; cases g y <;> simp
  rw [hnot] at hg' ⊢
  push_cast
  unfold weight
  nlinarith

private def pEmbedding (p q r : ℕ) : (Fin q × Fin r) ↪ Line p q r where
  toFun yz := .pLine yz.1 yz.2
  inj' := by intro a b h; cases a; cases b; simpa using h

private def qEmbedding (p q r : ℕ) : (Fin p × Fin r) ↪ Line p q r where
  toFun xz := .qLine xz.1 xz.2
  inj' := by intro a b h; cases a; cases b; simpa using h

private def rEmbedding (p q r : ℕ) : (Fin p × Fin q) ↪ Line p q r where
  toFun xy := .rLine xy.1 xy.2
  inj' := by intro a b h; cases a; cases b; simpa using h

theorem mask_counts {p q r : ℕ} (α : Fin p → Bool) (β : Fin q → Bool)
    (γ : Fin r → Bool) :
    counts (mask α β γ) = UniversalSynthesis.parity p q r (weight α) (weight β) (weight γ) := by
  classical
  have hP : ((mask α β γ).filter
      (fun l => match l with | .pLine _ _ => True | _ => False)) =
      (Finset.univ.filter fun yz : Fin q × Fin r => β yz.1 ≠ γ yz.2).map
        (pEmbedding p q r) := by
    ext l
    cases l <;> simp [mask, pEmbedding]
  have hQ : ((mask α β γ).filter
      (fun l => match l with | .qLine _ _ => True | _ => False)) =
      (Finset.univ.filter fun xz : Fin p × Fin r => α xz.1 ≠ γ xz.2).map
        (qEmbedding p q r) := by
    ext l
    cases l <;> simp [mask, qEmbedding]
  have hR : ((mask α β γ).filter
      (fun l => match l with | .rLine _ _ => True | _ => False)) =
      (Finset.univ.filter fun xy : Fin p × Fin q => α xy.1 ≠ β xy.2).map
        (rEmbedding p q r) := by
    ext l
    cases l <;> simp [mask, rEmbedding]
  ext i
  fin_cases i
  · change (((mask α β γ).filter
      (fun l => match l with | .pLine _ _ => True | _ => False)).card : ℤ) = _
    calc
      _ = ((Finset.univ.filter fun yz : Fin q × Fin r => β yz.1 ≠ γ yz.2).card : ℤ) := by
        exact_mod_cast (congrArg Finset.card hP).trans (Finset.card_map _)
      _ = _ := xor_card β γ
  · change (((mask α β γ).filter
      (fun l => match l with | .qLine _ _ => True | _ => False)).card : ℤ) = _
    calc
      _ = ((Finset.univ.filter fun xz : Fin p × Fin r => α xz.1 ≠ γ xz.2).card : ℤ) := by
        exact_mod_cast (congrArg Finset.card hQ).trans (Finset.card_map _)
      _ = _ := xor_card α γ
  · change (((mask α β γ).filter
      (fun l => match l with | .rLine _ _ => True | _ => False)).card : ℤ) = _
    calc
      _ = ((Finset.univ.filter fun xy : Fin p × Fin q => α xy.1 ≠ β xy.2).card : ℤ) := by
        exact_mod_cast (congrArg Finset.card hR).trans (Finset.card_map _)
      _ = _ := xor_card α β

theorem counts_nonneg {p q r : ℕ} (S : Finset (Line p q r)) (i : Fin 3) :
    0 ≤ counts S i := by
  fin_cases i <;> simp [counts]

theorem count_p_pos {p q r : ℕ} (S : Finset (Line p q r)) :
    0 < counts S 0 ↔ ∃ y z, Line.pLine y z ∈ S := by
  classical
  change 0 < (((S.filter (fun l => match l with | .pLine _ _ => True | _ => False)).card : ℕ) : ℤ) ↔ _
  rw [Nat.cast_pos, Finset.card_pos]
  constructor
  · rintro ⟨l, hl⟩
    cases l with
    | pLine y z => exact ⟨y, z, (Finset.mem_filter.mp hl).1⟩
    | qLine x z => simp at hl
    | rLine x y => simp at hl
  · rintro ⟨y, z, h⟩
    exact ⟨.pLine y z, by simp [h]⟩

theorem count_q_pos {p q r : ℕ} (S : Finset (Line p q r)) :
    0 < counts S 1 ↔ ∃ x z, Line.qLine x z ∈ S := by
  classical
  change 0 < (((S.filter (fun l => match l with | .qLine _ _ => True | _ => False)).card : ℕ) : ℤ) ↔ _
  rw [Nat.cast_pos, Finset.card_pos]
  constructor
  · rintro ⟨l, hl⟩
    cases l with
    | pLine y z => simp at hl
    | qLine x z => exact ⟨x, z, (Finset.mem_filter.mp hl).1⟩
    | rLine x y => simp at hl
  · rintro ⟨x, z, h⟩
    exact ⟨.qLine x z, by simp [h]⟩

theorem count_r_pos {p q r : ℕ} (S : Finset (Line p q r)) :
    0 < counts S 2 ↔ ∃ x y, Line.rLine x y ∈ S := by
  classical
  change 0 < (((S.filter (fun l => match l with | .rLine _ _ => True | _ => False)).card : ℕ) : ℤ) ↔ _
  rw [Nat.cast_pos, Finset.card_pos]
  constructor
  · rintro ⟨l, hl⟩
    cases l with
    | pLine y z => simp at hl
    | qLine x z => simp at hl
    | rLine x y => exact ⟨x, y, (Finset.mem_filter.mp hl).1⟩
  · rintro ⟨x, y, h⟩
    exact ⟨.rLine x y, by simp [h]⟩

theorem site_filter {p q r : ℕ} (S : Finset (Line p q r)) (s : Site p q r) :
    S.filter (fun l => covers l s) =
      ({.pLine s.2.1 s.2.2, .qLine s.1 s.2.2, .rLine s.1 s.2.1} :
        Finset (Line p q r)).filter (fun l => l ∈ S) := by
  classical
  ext l
  cases l <;> simp [covers, and_comm, and_left_comm, eq_comm]

theorem Paired.parity {p q r : ℕ} {S : Finset (Line p q r)} (h : Paired S)
    (x : Fin p) (y : Fin q) (z : Fin r) :
    Chemistry.bitXor
      (Chemistry.bitXor (decide (.pLine y z ∈ S)) (decide (.qLine x z ∈ S)))
      (decide (.rLine x y ∈ S)) = false := by
  classical
  have hs := h (x, y, z)
  rw [site_filter] at hs
  by_cases hP : .pLine y z ∈ S <;> by_cases hQ : .qLine x z ∈ S <;>
    by_cases hR : .rLine x y ∈ S <;>
    simp_all [Chemistry.bitXor, Finset.filter_insert, Finset.filter_singleton]

theorem Paired.mask_exists {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    {S : Finset (Line p q r)} (h : Paired S) :
    ∃ α β γ, S = mask α β γ := by
  classical
  obtain ⟨α, β, γ, hA, hB, hC⟩ := Chemistry.parity_factorization
    (⟨0, hp⟩ : Fin p) (⟨0, hq⟩ : Fin q) (⟨0, hr⟩ : Fin r)
    (fun y z => decide (.pLine y z ∈ S))
    (fun x z => decide (.qLine x z ∈ S))
    (fun x y => decide (.rLine x y ∈ S)) h.parity
  refine ⟨α, β, γ, ?_⟩
  ext l
  cases l with
  | pLine y z =>
    have hh := hA y z
    by_cases hl : .pLine y z ∈ S <;> cases hb : β y <;> cases hg : γ z <;>
      simp_all [mask, Chemistry.bitXor]
  | qLine x z =>
    have hh := hB x z
    by_cases hl : .qLine x z ∈ S <;> cases ha : α x <;> cases hg : γ z <;>
      simp_all [mask, Chemistry.bitXor]
  | rLine x y =>
    have hh := hC x y
    by_cases hl : .rLine x y ∈ S <;> cases ha : α x <;> cases hb : β y <;>
      simp_all [mask, Chemistry.bitXor]

end CyclicAtoms.PrimeGrid
