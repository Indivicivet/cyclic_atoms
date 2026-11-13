import Mathlib.Tactic

namespace CyclicAtoms.UniversalSynthesis

/-- Element counts in the order p, q, r. Integers avoid truncated subtraction
in the parity identities; `Valid` restricts these to molecular formulas. -/
abbrev Formula := Fin 3 → ℤ

def parity (p q r a b c : ℤ) : Formula :=
  ![b * (r - c) + (q - b) * c,
    a * (r - c) + (p - a) * c,
    a * (q - b) + (p - a) * b]

def binaryPQ (p q : ℤ) : Formula := ![q, p, 0]
def binaryPR (p r : ℤ) : Formula := ![r, 0, p]
def binaryQR (q r : ℤ) : Formula := ![0, r, q]
def dimerP : Formula := ![2, 0, 0]
def dimerQ : Formula := ![0, 2, 0]
def dimerR : Formula := ![0, 0, 2]

/-- The three dimers, the three connected binaries, and all positive
three-element parity profiles. This is a formula-level catalog. -/
def Valid (p q r : ℤ) (f : Formula) : Prop :=
  f ∈ [dimerP, dimerQ, dimerR, binaryPQ p q, binaryPR p r, binaryQR q r] ∨
    ∃ a b c : ℤ, 0 ≤ a ∧ a ≤ p ∧ 0 ≤ b ∧ b ≤ q ∧ 0 ≤ c ∧ c ≤ r ∧
      (∀ i, 0 < parity p q r a b c i) ∧ f = parity p q r a b c

/-- A finite production tree. Both outputs must be valid molecules; the
unused output is retained when this tree is realized as a stock execution. -/
inductive Reachable (legal : Formula → Prop) (feeds : List Formula) : Formula → Prop
  | feed {f} : f ∈ feeds → Reachable legal feeds f
  | react {x y z w} : Reachable legal feeds x → Reachable legal feeds y →
      legal z → legal w → x + y = z + w → Reachable legal feeds z

private theorem cross_pos {m n x y : ℤ} (hn : 0 < n)
    (hx : 0 < x) (hxm : x < m) (hy : 0 ≤ y) (hyn : y ≤ n) :
    0 < x * (n - y) + (m - x) * y := by
  by_cases h : y = 0
  · subst y; simpa using mul_pos hx hn
  · have hp := mul_pos (sub_pos.mpr hxm) (lt_of_le_of_ne hy (Ne.symm h))
    have hz := mul_nonneg (le_of_lt hx) (sub_nonneg.mpr hyn)
    linarith

private theorem cross_comm (m n x y : ℤ) :
    x * (n - y) + (m - x) * y = y * (m - x) + (n - y) * x := by ring

private theorem valid_two_interior {p q r a b c : ℤ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (ha : 0 ≤ a) (hap : a ≤ p) (hb : 0 ≤ b) (hbq : b ≤ q)
    (hc : 0 ≤ c) (hcr : c ≤ r)
    (hi : (0 < a ∧ a < p) ∧ (0 < b ∧ b < q) ∨
      (0 < a ∧ a < p) ∧ (0 < c ∧ c < r) ∨
      (0 < b ∧ b < q) ∧ (0 < c ∧ c < r)) :
    Valid p q r (parity p q r a b c) := by
  refine Or.inr ⟨a, b, c, ha, hap, hb, hbq, hc, hcr, ?_, rfl⟩
  intro i
  fin_cases i <;> simp only [parity, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons]
  all_goals rcases hi with ⟨hai, hbi⟩ | ⟨hai, hci⟩ | ⟨hbi, hci⟩
  all_goals solve
    | exact cross_pos hr hbi.1 hbi.2 hc hcr
    | exact cross_pos hr hai.1 hai.2 hc hcr
    | exact cross_pos hq hai.1 hai.2 hb hbq
    | exact (cross_comm q r b c).symm ▸ cross_pos hq hci.1 hci.2 hb hbq
    | exact (cross_comm p r a c).symm ▸ cross_pos hp hci.1 hci.2 ha hap
    | exact (cross_comm p q a b).symm ▸ cross_pos hp hbi.1 hbi.2 ha hap

private theorem midpoint_a (p q r a b c : ℤ) :
    parity p q r a b c + parity p q r a b c =
      parity p q r (a - 1) b c + parity p q r (a + 1) b c := by
  ext i; fin_cases i <;> simp [parity] <;> ring

private theorem midpoint_b (p q r a b c : ℤ) :
    parity p q r a b c + parity p q r a b c =
      parity p q r a (b - 1) c + parity p q r a (b + 1) c := by
  ext i; fin_cases i <;> simp [parity] <;> ring

private theorem midpoint_c (p q r a b c : ℤ) :
    parity p q r a b c + parity p q r a b c =
      parity p q r a b (c - 1) + parity p q r a b (c + 1) := by
  ext i; fin_cases i <;> simp [parity] <;> ring

/-- Repeated midpoint reactions spread a seed at 1 across a legal interval. -/
private theorem walk {legal : Formula → Prop} {feeds : List Formula}
    (f : ℤ → Formula) (N : ℤ) (hN : 2 ≤ N)
    (hv : ∀ n, 0 ≤ n → n ≤ N → legal (f n))
    (hm : ∀ n, f n + f n = f (n - 1) + f (n + 1))
    (hseed : Reachable legal feeds (f 1)) :
    ∀ n, 0 ≤ n → n ≤ N → Reachable legal feeds (f n) := by
  have hz : Reachable legal feeds (f 0) :=
    Reachable.react hseed hseed (hv 0 (by omega) (by omega))
      (hv 2 (by omega) hN) (by simpa using hm 1)
  have hall : ∀ n : ℕ, (n : ℤ) ≤ N → Reachable legal feeds (f n) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => intro _; exact hz
    | one => intro _; exact hseed
    | more n _ ih =>
      intro hn
      push_cast at hn
      have hprev := ih (by omega)
      apply Reachable.react hprev hprev (hv ((n : ℤ) + 2) (by omega) (by omega)) (hv n (by omega) (by omega))
      have h := hm ((n : ℤ) + 1)
      simpa only [Nat.cast_add, Nat.cast_ofNat, add_sub_cancel_right,
        show (n : ℤ) + 1 + 1 = n + 2 by ring] using h.trans (add_comm _ _)
  intro n hn hnN
  lift n to ℕ using hn
  exact hall n hnN

private theorem valid_strip_c {p q r c : ℤ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hr : 2 ≤ r) (hc : 0 ≤ c) (hcr : c ≤ r) :
    Valid p q r (parity p q r 0 1 c) := by
  by_cases h : c = 0
  · subst c; left; simp [parity, binaryPR, dimerP, dimerQ, dimerR, binaryPQ, binaryQR]
  · refine Or.inr ⟨0, 1, c, by omega, by omega, by omega, by omega, hc, hcr, ?_, rfl⟩
    intro i; fin_cases i <;> simp [parity]
    · simpa using (cross_pos (m := q) (n := r) (x := 1) (y := c) (by omega) (by omega) (by omega) hc hcr)
    · exact mul_pos (by omega) (by omega)
    · omega

private theorem valid_strip_b {p q r b : ℤ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hr : 2 ≤ r) (hb : 0 ≤ b) (hbq : b ≤ q) :
    Valid p q r (parity p q r 0 b 1) := by
  by_cases h : b = 0
  · subst b; left; simp [parity, binaryPQ, dimerP, dimerQ, dimerR, binaryPR, binaryQR]
  · refine Or.inr ⟨0, b, 1, by omega, by omega, hb, hbq, by omega, by omega, ?_, rfl⟩
    intro i; fin_cases i <;> simp [parity]
    · simpa [add_comm, mul_comm] using (cross_pos (m := r) (n := q) (x := 1) (y := b) (by omega) (by omega) (by omega) hb hbq)
    · omega
    · exact mul_pos (by omega) (by omega)

/-- Seeds and midpoint reactions reach every profile with two interior
weights. Only dimensions at least two are needed for this part. -/
theorem interior_reachable (p q r : ℤ) (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r) :
    ∀ a b c, 0 < a → a < p → 0 < b → b < q → 0 ≤ c → c ≤ r →
      Reachable (Valid p q r) [binaryPQ p q, binaryPR p r] (parity p q r a b c) := by
  let P := Reachable (Valid p q r) [binaryPQ p q, binaryPR p r]
  have hPQ : P (binaryPQ p q) := .feed (by simp)
  have hPR : P (binaryPR p r) := .feed (by simp)
  have hDp : Valid p q r dimerP := Or.inl (by simp)
  have hseed0 : P (parity p q r 0 1 1) := by
    apply Reachable.react hPQ hPR (valid_strip_c (by omega) (by omega) hr (by omega)
      (by omega)) hDp
    ext i; fin_cases i <;> simp [parity, binaryPQ, binaryPR, dimerP]
    all_goals ring
  have hstripC : ∀ c, 0 ≤ c → c ≤ r → P (parity p q r 0 1 c) :=
    walk _ r hr (fun c hc hcr => valid_strip_c (by omega) (by omega) hr hc hcr)
      (midpoint_c p q r 0 1) hseed0
  have hstripB : ∀ b, 0 ≤ b → b ≤ q → P (parity p q r 0 b 1) :=
    walk _ q (by omega) (fun b hb hbq => valid_strip_b (by omega) (by omega) hr hb hbq)
      (fun b => midpoint_b p q r 0 b 1) hseed0
  have hv (a b c : ℤ) (ha : 0 ≤ a) (hap : a ≤ p) (hb : 0 ≤ b) (hbq : b ≤ q)
      (hc : 0 ≤ c) (hcr : c ≤ r)
      (hi : (0 < a ∧ a < p) ∧ (0 < b ∧ b < q) ∨
        (0 < a ∧ a < p) ∧ (0 < c ∧ c < r) ∨
        (0 < b ∧ b < q) ∧ (0 < c ∧ c < r)) :=
    valid_two_interior (by omega) (by omega) (by omega) ha hap hb hbq hc hcr hi
  have hseed1 : P (parity p q r 1 (q - 1) 1) := by
    apply Reachable.react (hstripC (r - 1) (by omega) (by omega))
      (hstripB (q - 1) (by omega) (by omega))
      (hv 1 (q - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (Or.inl ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩))
      (hv 1 1 (r - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (Or.inl ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩))
    ext i; fin_cases i <;> simp [parity] <;> ring
  have hseed : P (parity p q r 1 1 1) := by
    have h := walk (fun b => parity p q r 1 (q - b) 1) q (by omega)
      (fun b hb hbq => hv 1 (q - b) 1 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (Or.inr (Or.inl ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩)))
      (fun b => by ext i; fin_cases i <;> simp [parity] <;> ring) hseed1
    simpa using h (q - 1) (by omega) (by omega)
  have hA : ∀ a, 0 ≤ a → a ≤ p → P (parity p q r a 1 1) :=
    walk _ p (by omega)
      (fun a ha hap => hv a 1 1 ha hap (by omega) (by omega) (by omega) (by omega)
        (Or.inr (Or.inr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩)))
      (fun a => midpoint_a p q r a 1 1) hseed
  have hAB : ∀ a b, 0 < a → a < p → 0 ≤ b → b ≤ q → P (parity p q r a b 1) := by
    intro a b ha hap hb hbq
    exact walk _ q (by omega)
      (fun b hb hbq => hv a b 1 (by omega) (by omega) hb hbq (by omega) (by omega)
        (Or.inr (Or.inl ⟨⟨ha, hap⟩, ⟨by omega, by omega⟩⟩)))
      (fun b => midpoint_b p q r a b 1) (hA a (by omega) (by omega)) b hb hbq
  have hABC : ∀ a b c, 0 < a → a < p → 0 < b → b < q → 0 ≤ c → c ≤ r →
      P (parity p q r a b c) := by
    intro a b c ha hap hb hbq hc hcr
    exact walk _ r hr
      (fun c hc hcr => hv a b c (by omega) (by omega) (by omega) (by omega) hc hcr
        (Or.inl ⟨⟨ha, hap⟩, ⟨hb, hbq⟩⟩))
      (midpoint_c p q r a b) (hAB a b ha hap (by omega) (by omega)) c hc hcr
  exact hABC

theorem missing_binary (p q r : ℤ) (hp : 2 ≤ p) (hq : 3 ≤ q) (hr : 2 ≤ r) :
    Reachable (Valid p q r) [binaryPQ p q, binaryPR p r] (binaryQR q r) := by
  have h := interior_reachable p q r hp (by omega) hr 1 1 0
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  apply Reachable.react h h (Or.inl (by simp))
    (valid_two_interior (by omega) (by omega) (by omega)
      (a := 1) (b := 2) (c := 0)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (Or.inl ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩))
  ext i; fin_cases i <;> simp [parity, binaryQR] <;> ring

/-- A parametric construction from the two feeds sharing p. -/
theorem every_valid_formula (p q r : ℤ) (hp : 3 ≤ p) (hq : 3 ≤ q) (hr : 2 ≤ r)
    (f : Formula) (hf : Valid p q r f) :
    Reachable (Valid p q r) [binaryPQ p q, binaryPR p r] f := by
  classical
  let P := Reachable (Valid p q r) [binaryPQ p q, binaryPR p r]
  have hPQ : P (binaryPQ p q) := .feed (by simp)
  have hPR : P (binaryPR p r) := .feed (by simp)
  have hDp : Valid p q r dimerP := Or.inl (by simp)
  have hDq : Valid p q r dimerQ := Or.inl (by simp)
  have hDr : Valid p q r dimerR := Or.inl (by simp)
  have hv (a b c : ℤ) (ha : 0 ≤ a) (hap : a ≤ p) (hb : 0 ≤ b) (hbq : b ≤ q)
      (hc : 0 ≤ c) (hcr : c ≤ r)
      (hi : (0 < a ∧ a < p) ∧ (0 < b ∧ b < q) ∨
        (0 < a ∧ a < p) ∧ (0 < c ∧ c < r) ∨
        (0 < b ∧ b < q) ∧ (0 < c ∧ c < r)) :=
    valid_two_interior (by omega) (by omega) (by omega) ha hap hb hbq hc hcr hi
  have hABC := interior_reachable p q r (by omega) (by omega) hr
  have hACB : ∀ a b c, 0 < a → a < p → 0 ≤ b → b ≤ q → 0 < c → c < r →
      P (parity p q r a b c) := by
    intro a b c ha hap hb hbq hc hcr
    exact walk _ q (by omega)
      (fun b hb hbq => hv a b c (by omega) (by omega) hb hbq (by omega) (by omega)
        (Or.inr (Or.inl ⟨⟨ha, hap⟩, ⟨hc, hcr⟩⟩)))
      (fun b => midpoint_b p q r a b c)
      (hABC a 1 c ha hap (by omega) (by omega) (by omega) (by omega)) b hb hbq
  have hBCA : ∀ a b c, 0 ≤ a → a ≤ p → 0 < b → b < q → 0 < c → c < r →
      P (parity p q r a b c) := by
    intro a b c ha hap hb hbq hc hcr
    exact walk _ p (by omega)
      (fun a ha hap => hv a b c ha hap (by omega) (by omega) (by omega) (by omega)
        (Or.inr (Or.inr ⟨⟨hb, hbq⟩, ⟨hc, hcr⟩⟩)))
      (fun a => midpoint_a p q r a b c)
      (hABC 1 b c (by omega) (by omega) hb hbq (by omega) (by omega)) a ha hap
  -- The remaining profiles lie on edges. Splitting at the adjacent interior
  -- weight reaches an endpoint without ever using a disconnected profile.
  have hpositive : ∀ a b c, 0 ≤ a → a ≤ p → 0 ≤ b → b ≤ q → 0 ≤ c → c ≤ r →
      (∀ i, 0 < parity p q r a b c i) → P (parity p q r a b c) := by
    intro a b c ha hap hb hbq hc hcr hpos
    have hlegal : Valid p q r (parity p q r a b c) :=
      Or.inr ⟨a, b, c, ha, hap, hb, hbq, hc, hcr, hpos, rfl⟩
    by_cases hai : 0 < a ∧ a < p
    · by_cases hbi : 0 < b ∧ b < q
      · exact hABC a b c hai.1 hai.2 hbi.1 hbi.2 hc hcr
      by_cases hci : 0 < c ∧ c < r
      · exact hACB a b c hai.1 hai.2 hb hbq hci.1 hci.2
      have hcases : (b = 0 ∧ c = r) ∨ (b = q ∧ c = 0) := by
        have h := hpos 0
        simp [parity] at h
        rcases (show b = 0 ∨ b = q by omega) with hbz | hbz <;> simp only [hbz] at * <;>
          rcases (show c = 0 ∨ c = r by omega) with hcz | hcz <;> simp only [hcz] at * <;> simp_all
      rcases hcases with ⟨hb0, hcR⟩ | ⟨hbQ, hc0⟩
      · subst b; subst c
        apply Reachable.react (hABC a 1 r hai.1 hai.2 (by omega) (by omega) (by omega) (by omega))
          (hABC a 1 r hai.1 hai.2 (by omega) (by omega) (by omega) (by omega)) hlegal
          (hv a 2 r ha hap (by omega) (by omega) (by omega) (by omega)
            (Or.inl ⟨hai, ⟨by omega, by omega⟩⟩))
        simpa using midpoint_b p q r a 1 r
      · subst b; subst c
        apply Reachable.react (hABC a (q - 1) 0 hai.1 hai.2 (by omega) (by omega) (by omega) (by omega))
          (hABC a (q - 1) 0 hai.1 hai.2 (by omega) (by omega) (by omega) (by omega)) hlegal
          (hv a (q - 2) 0 ha hap (by omega) (by omega) (by omega) (by omega)
            (Or.inl ⟨hai, ⟨by omega, by omega⟩⟩))
        have h := midpoint_b p q r a (q - 1) 0
        simpa only [show q - 1 - 1 = q - 2 by omega, show q - 1 + 1 = q by omega] using h.trans (add_comm _ _)
    · by_cases hbi : 0 < b ∧ b < q
      · by_cases hci : 0 < c ∧ c < r
        · exact hBCA a b c ha hap hbi.1 hbi.2 hci.1 hci.2
        rcases (show a = 0 ∨ a = p by omega) with haz | haz <;> simp only [haz] at *
        · apply Reachable.react (hABC 1 b c (by omega) (by omega) hbi.1 hbi.2 hc hcr)
            (hABC 1 b c (by omega) (by omega) hbi.1 hbi.2 hc hcr) hlegal
            (hv 2 b c (by omega) (by omega) hb hbq hc hcr
              (Or.inl ⟨⟨by omega, by omega⟩, hbi⟩))
          simpa using midpoint_a p q r 1 b c
        · apply Reachable.react (hABC (p - 1) b c (by omega) (by omega) hbi.1 hbi.2 hc hcr)
            (hABC (p - 1) b c (by omega) (by omega) hbi.1 hbi.2 hc hcr) hlegal
            (hv (p - 2) b c (by omega) (by omega) hb hbq hc hcr
              (Or.inl ⟨⟨by omega, by omega⟩, hbi⟩))
          have h := midpoint_a p q r (p - 1) b c
          simpa only [show p - 1 - 1 = p - 2 by omega, show p - 1 + 1 = p by omega] using h.trans (add_comm _ _)
      · have hci : 0 < c ∧ c < r := by
          apply Classical.byContradiction
          intro hn
          have h0 := hpos 0
          have h1 := hpos 1
          have h2 := hpos 2
          rcases (show a = 0 ∨ a = p by omega) with haz | haz <;>
            rcases (show b = 0 ∨ b = q by omega) with hbz | hbz <;>
            rcases (show c = 0 ∨ c = r by omega) with hcz | hcz
          all_goals simp [parity, haz, hbz, hcz] at h0 h1 h2
        rcases (show a = 0 ∨ a = p by omega) with haz | haz <;> simp only [haz] at *
        · apply Reachable.react (hACB 1 b c (by omega) (by omega) hb hbq hci.1 hci.2)
            (hACB 1 b c (by omega) (by omega) hb hbq hci.1 hci.2) hlegal
            (hv 2 b c (by omega) (by omega) hb hbq hc hcr
              (Or.inr (Or.inl ⟨⟨by omega, by omega⟩, hci⟩)))
          simpa using midpoint_a p q r 1 b c
        · apply Reachable.react (hACB (p - 1) b c (by omega) (by omega) hb hbq hci.1 hci.2)
            (hACB (p - 1) b c (by omega) (by omega) hb hbq hci.1 hci.2) hlegal
            (hv (p - 2) b c (by omega) (by omega) hb hbq hc hcr
              (Or.inr (Or.inl ⟨⟨by omega, by omega⟩, hci⟩)))
          have h := midpoint_a p q r (p - 1) b c
          simpa only [show p - 1 - 1 = p - 2 by omega, show p - 1 + 1 = p by omega] using h.trans (add_comm _ _)
  have hQR : P (binaryQR q r) := missing_binary p q r (by omega) hq hr
  rcases hf with hf | ⟨a, b, c, ha, hap, hb, hbq, hc, hcr, hpos, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · apply Reachable.react hPQ hPR hDp (valid_strip_c (p := p) (q := q) (c := 1) (by omega) (by omega) hr (by omega) (by omega))
      ext i; fin_cases i <;> simp [parity, binaryPQ, binaryPR, dimerP]
      all_goals ring
    · apply Reachable.react hPQ hQR hDq
        (Or.inr ⟨1, 0, 1, by omega, by omega, by omega, by omega, by omega, by omega,
          by intro i; fin_cases i <;> simp [parity] <;> omega, rfl⟩)
      ext i; fin_cases i <;> simp [parity, binaryPQ, binaryQR, dimerQ]
      all_goals ring
    · apply Reachable.react hPR hQR hDr
        (Or.inr ⟨1, 1, 0, by omega, by omega, by omega, by omega, by omega, by omega,
          by intro i; fin_cases i <;> simp [parity] <;> omega, rfl⟩)
      ext i; fin_cases i <;> simp [parity, binaryPR, binaryQR, dimerR]
      all_goals ring
    · exact hPQ
    · exact hPR
    · exact hQR
  · exact hpositive a b c ha hap hb hbq hc hcr hpos

theorem Reachable.map {legal legal' : Formula → Prop} {feeds feeds' : List Formula}
    (T : Formula → Formula) (hadd : ∀ x y, T (x + y) = T x + T y)
    (hl : ∀ f, legal f → legal' (T f))
    (hf : ∀ f ∈ feeds, Reachable legal' feeds' (T f))
    {f : Formula} (h : Reachable legal feeds f) : Reachable legal' feeds' (T f) := by
  induction h with
  | feed h => exact hf _ h
  | react _ _ hz hw balance ihx ihy =>
    apply Reachable.react ihx ihy (hl _ hz) (hl _ hw)
    rw [← hadd, ← hadd, balance]

private def swap (f : Formula) : Formula := ![f 1, f 0, f 2]
private def rotate (f : Formula) : Formula := ![f 1, f 2, f 0]

private theorem swap_valid {p q r : ℤ} {f : Formula} (h : Valid q p r f) :
    Valid p q r (swap f) := by
  rcases h with h | ⟨a, b, c, ha, haq, hb, hbp, hc, hcr, hpos, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals left; simp [swap, dimerP, dimerQ, dimerR, binaryPQ, binaryPR, binaryQR]
  · have heq : swap (parity q p r a b c) = parity p q r b a c := by
      ext i; fin_cases i <;> simp [swap, parity]
      all_goals ring
    refine Or.inr ⟨b, a, c, hb, hbp, ha, haq, hc, hcr, ?_, heq⟩
    intro i
    rw [← heq]
    fin_cases i
    · exact hpos 1
    · exact hpos 0
    · exact hpos 2

private theorem rotate_valid {p q r : ℤ} {f : Formula} (h : Valid r p q f) :
    Valid p q r (rotate f) := by
  rcases h with h | ⟨a, b, c, ha, har, hb, hbp, hc, hcq, hpos, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals left; simp [rotate, dimerP, dimerQ, dimerR, binaryPQ, binaryPR, binaryQR]
  · have heq : rotate (parity r p q a b c) = parity p q r b c a := by
      ext i; fin_cases i <;> simp [rotate, parity] <;> ring
    refine Or.inr ⟨b, c, a, hb, hbp, hc, hcq, ha, har, ?_, heq⟩
    intro i
    rw [← heq]
    fin_cases i
    · exact hpos 1
    · exact hpos 2
    · exact hpos 0

def feedPair (p q r : ℤ) (i : Fin 3) : List Formula :=
  ![[binaryPQ p q, binaryPR p r], [binaryPQ p q, binaryQR q r],
    [binaryPR p r, binaryQR q r]] i

/-- Any two binary feeds suffice. The dimensions can be relabeled so that
the possible prime 2 is r; no primality assumption is needed for this algebra. -/
theorem every_valid_formula_from_any_pair (p q r : ℤ)
    (hp : 3 ≤ p) (hq : 3 ≤ q) (hr : 2 ≤ r) (pair : Fin 3)
    (f : Formula) (hf : Valid p q r f) :
    Reachable (Valid p q r) (feedPair p q r pair) f := by
  have hPQ : Reachable (Valid p q r) (feedPair p q r pair) (binaryPQ p q) := by
    fin_cases pair
    · exact .feed (by simp [feedPair])
    · exact .feed (by simp [feedPair])
    · have h := (missing_binary r p q hr hp (by omega)).map rotate
        (by intro x y; ext i; fin_cases i <;> rfl)
        (fun _ h => rotate_valid h)
        (feeds' := feedPair p q r 2) (by
          intro f hf
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
          rcases hf with rfl | rfl
          all_goals apply Reachable.feed; simp [rotate, feedPair, binaryPQ, binaryPR, binaryQR])
      simpa [rotate, binaryQR, binaryPQ] using h
  have hPR : Reachable (Valid p q r) (feedPair p q r pair) (binaryPR p r) := by
    fin_cases pair
    · exact .feed (by simp [feedPair])
    · have h := (missing_binary q p r (by omega) hp hr).map swap
        (by intro x y; ext i; fin_cases i <;> rfl)
        (fun _ h => swap_valid h)
        (feeds' := feedPair p q r 1) (by
          intro f hf
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
          rcases hf with rfl | rfl
          all_goals apply Reachable.feed; simp [swap, feedPair, binaryPQ, binaryPR, binaryQR])
      simpa [swap, binaryQR, binaryPR] using h
    · exact .feed (by simp [feedPair])
  exact (every_valid_formula p q r hp hq hr f hf).map id (by intros; rfl)
    (fun _ h => h) (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl
      · exact hPQ
      · exact hPR)

/-- A multiset retains multiplicities while ignoring the ordering of a stock. -/
inductive Step (legal : Formula → Prop) : Multiset Formula → Multiset Formula → Prop
  | replace (x y z w : Formula) (rest : Multiset Formula)
      (hz : legal z) (hw : legal w) (balance : x + y = z + w) :
      Step legal (x ::ₘ y ::ₘ rest) (z ::ₘ w ::ₘ rest)

inductive Chain (legal : Formula → Prop) : Multiset Formula → Multiset Formula → Prop
  | refl (stock) : Chain legal stock stock
  | step {a b c} : Step legal a b → Chain legal b c → Chain legal a c

/-- Conservation is coordinatewise, so it conserves each element separately. -/
theorem Step.conserves {legal : Formula → Prop} {a b : Multiset Formula}
    (h : Step legal a b) : a.sum = b.sum := by
  cases h with
  | replace x y z w rest hz hw balance =>
    simpa only [Multiset.sum_cons, ← add_assoc] using congrArg (· + rest.sum) balance

theorem Chain.conserves {legal : Formula → Prop} {a b : Multiset Formula}
    (h : Chain legal a b) : a.sum = b.sum := by
  induction h with
  | refl => rfl
  | step hs _ ih => exact hs.conserves.trans ih

theorem Chain.card_eq {legal : Formula → Prop} {a b : Multiset Formula}
    (h : Chain legal a b) : a.card = b.card := by
  induction h with
  | refl => rfl
  | step hs _ ih =>
    rw [← ih]
    cases hs
    simp

theorem Chain.trans {legal : Formula → Prop} {a b c : Multiset Formula}
    (hab : Chain legal a b) (hbc : Chain legal b c) : Chain legal a c := by
  induction hab with
  | refl => exact hbc
  | step hs _ ih => exact .step hs (ih hbc)

theorem Chain.add {legal : Formula → Prop} {a b : Multiset Formula}
    (h : Chain legal a b) (stock : Multiset Formula) :
    Chain legal (a + stock) (b + stock) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih =>
    apply Chain.step _ ih
    cases hs with
    | replace x y z w rest hz hw balance =>
      simpa only [Multiset.cons_add] using Step.replace x y z w (rest + stock) hz hw balance

/-- Production trees give finite sequential batches, using separate fresh
feed supplies for repeated inputs and retaining every unused output. -/
theorem Reachable.batch {legal : Formula → Prop} {feeds : List Formula} {target : Formula}
    (h : Reachable legal feeds target) :
    ∃ initial final : Multiset Formula,
      (∀ f ∈ initial, f ∈ feeds) ∧ Chain legal initial final ∧ target ∈ final := by
  induction h with
  | feed hf => exact ⟨{_}, {_}, by simpa, .refl _, by simp⟩
  | @react x y z w hx hy hz hw balance ihx ihy =>
    obtain ⟨ix, fx, hix, hcx, hfx⟩ := ihx
    obtain ⟨iy, fy, hiy, hcy, hfy⟩ := ihy
    obtain ⟨rx, rfl⟩ := Multiset.exists_cons_of_mem hfx
    obtain ⟨ry, rfl⟩ := Multiset.exists_cons_of_mem hfy
    refine ⟨ix + iy, z ::ₘ w ::ₘ (rx + ry), ?_, ?_, by simp⟩
    · intro f hf
      rcases Multiset.mem_add.mp hf with h | h
      · exact hix f h
      · exact hiy f h
    · apply (hcx.add iy).trans
      have hsecond := hcy.add (x ::ₘ rx)
      rw [add_comm iy, add_comm (y ::ₘ ry)] at hsecond
      apply hsecond.trans
      simpa only [Multiset.cons_add, Multiset.add_cons, Multiset.cons_swap] using
        (Chain.step (Step.replace x y z w (rx + ry) hz hw balance) (.refl _))

/-- The generalized universal synthesis theorem, including finite stocks
and byproducts, for the complete parity formula catalog. -/
theorem universal_synthesis (p q r : ℤ) (hp : 3 ≤ p) (hq : 3 ≤ q) (hr : 2 ≤ r)
    (pair : Fin 3) (target : Formula) (ht : Valid p q r target) :
    ∃ initial final : Multiset Formula,
      (∀ f ∈ initial, f ∈ feedPair p q r pair) ∧
      Chain (Valid p q r) initial final ∧ target ∈ final :=
  (every_valid_formula_from_any_pair p q r hp hq hr pair target ht).batch

/-- info: 'CyclicAtoms.UniversalSynthesis.universal_synthesis' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms universal_synthesis

end CyclicAtoms.UniversalSynthesis
