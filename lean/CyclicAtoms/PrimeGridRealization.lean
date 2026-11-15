import CyclicAtoms.PrimeGridCounting

namespace CyclicAtoms.PrimeGrid

theorem adj_symm {p q r : ℕ} {S : Finset (Line p q r)} {l m : Line p q r}
    (h : Adj S l m) : Adj S m l := by
  obtain ⟨hl, hm, s, hs, ht⟩ := h
  exact ⟨hm, hl, s, ht, hs⟩

private theorem pq_adj {p q r : ℕ} {S : Finset (Line p q r)}
    {x : Fin p} {y : Fin q} {z : Fin r}
    (hl : Line.pLine y z ∈ S) (hm : Line.qLine x z ∈ S) :
    Adj S (.pLine y z) (.qLine x z) := ⟨hl, hm, ⟨x, y, z⟩, by simp [covers]⟩

private theorem pr_adj {p q r : ℕ} {S : Finset (Line p q r)}
    {x : Fin p} {y : Fin q} {z : Fin r}
    (hl : Line.pLine y z ∈ S) (hm : Line.rLine x y ∈ S) :
    Adj S (.pLine y z) (.rLine x y) := ⟨hl, hm, ⟨x, y, z⟩, by simp [covers]⟩

private theorem qr_adj {p q r : ℕ} {S : Finset (Line p q r)}
    {x : Fin p} {y : Fin q} {z : Fin r}
    (hl : Line.qLine x z ∈ S) (hm : Line.rLine x y ∈ S) :
    Adj S (.qLine x z) (.rLine x y) := ⟨hl, hm, ⟨x, y, z⟩, by simp [covers]⟩

theorem mask_paired {p q r : ℕ} (α : Fin p → Bool) (β : Fin q → Bool)
    (γ : Fin r → Bool) : Paired (mask α β γ) := by
  classical
  intro ⟨x, y, z⟩
  have hset : (mask α β γ).filter (fun l => covers l (x, y, z)) =
      ({.pLine y z, .qLine x z, .rLine x y} : Finset (Line p q r)).filter
        (fun l => l ∈ mask α β γ) := by
    ext l
    cases l <;> simp [covers, mask] <;> aesop
  rw [hset]
  simp only [Finset.filter_insert, Finset.filter_singleton]
  cases hx : α x <;> cases hy : β y <;> cases hz : γ z <;>
    simp [mask, hx, hy, hz]

/-- A three-class path joins all lines of its classes. The other classes
attach to it; actual coordinate indices, not only the six class names,
are accounted for in these paths. -/
private theorem connected_of_backbone {p q r : ℕ}
    (α : Fin p → Bool) (β : Fin q → Bool) (γ : Fin r → Bool)
    (x0 : Fin p) (y1 : Fin q) (z0 z1 : Fin r)
    (hx0 : α x0 = false) (hy1 : β y1 = true)
    (hz0 : γ z0 = false) (hz1 : γ z1 = true) : Connected (mask α β γ) := by
  classical
  let S := mask α β γ
  have hroot : Line.rLine x0 y1 ∈ S := by simp [S, mask, hx0, hy1]
  have hB (x : Fin p) (z : Fin r) (hx : α x = false) (hz : γ z = true) :
      Relation.ReflTransGen (Adj S) (.qLine x z) (.rLine x0 y1) := by
    have hb : Line.qLine x z ∈ S := by simp [S, mask, hx, hz]
    have hc : Line.rLine x y1 ∈ S := by simp [S, mask, hx, hy1]
    have ha : Line.pLine y1 z0 ∈ S := by simp [S, mask, hy1, hz0]
    exact (Relation.ReflTransGen.single (qr_adj hb hc)).trans
      ((Relation.ReflTransGen.single (adj_symm (pr_adj ha hc))).trans
        (Relation.ReflTransGen.single (pr_adj ha hroot)))
  have hA (y : Fin q) (z : Fin r) (hy : β y = true) (hz : γ z = false) :
      Relation.ReflTransGen (Adj S) (.pLine y z) (.rLine x0 y1) := by
    have ha : Line.pLine y z ∈ S := by simp [S, mask, hy, hz]
    have hc : Line.rLine x0 y ∈ S := by simp [S, mask, hx0, hy]
    have hb : Line.qLine x0 z1 ∈ S := by simp [S, mask, hx0, hz1]
    exact (Relation.ReflTransGen.single (pr_adj ha hc)).trans
      ((Relation.ReflTransGen.single (adj_symm (qr_adj hb hc))).trans
        (hB x0 z1 hx0 hz1))
  have hall : ∀ l ∈ S, Relation.ReflTransGen (Adj S) l (.rLine x0 y1) := by
    intro l hl
    cases l with
    | pLine y z =>
      have hne : β y ≠ γ z := by simpa [S, mask] using hl
      cases hy : β y <;> cases hz : γ z
      · exact False.elim (hne (hy.trans hz.symm))
      · have hb : Line.qLine x0 z ∈ S := by simp [S, mask, hx0, hz]
        exact (Relation.ReflTransGen.single (pq_adj hl hb)).trans (hB x0 z hx0 hz)
      · exact hA y z hy hz
      · exact False.elim (hne (hy.trans hz.symm))
    | qLine x z =>
      have hne : α x ≠ γ z := by simpa [S, mask] using hl
      cases hx : α x <;> cases hz : γ z
      · exact False.elim (hne (hx.trans hz.symm))
      · exact hB x z hx hz
      · have ha : Line.pLine y1 z ∈ S := by simp [S, mask, hy1, hz]
        exact (Relation.ReflTransGen.single (adj_symm (pq_adj ha hl))).trans
          (hA y1 z hy1 hz)
      · exact False.elim (hne (hx.trans hz.symm))
    | rLine x y =>
      have hne : α x ≠ β y := by simpa [S, mask] using hl
      cases hx : α x <;> cases hy : β y
      · exact False.elim (hne (hx.trans hy.symm))
      · have hb : Line.qLine x z1 ∈ S := by simp [S, mask, hx, hz1]
        exact (Relation.ReflTransGen.single (adj_symm (qr_adj hb hl))).trans
          (hB x z1 hx hz1)
      · have ha : Line.pLine y z1 ∈ S := by simp [S, mask, hy, hz1]
        have hb : Line.qLine x0 z1 ∈ S := by simp [S, mask, hx0, hz1]
        exact (Relation.ReflTransGen.single (adj_symm (pr_adj ha hl))).trans
          ((Relation.ReflTransGen.single (pq_adj ha hb)).trans (hB x0 z1 hx0 hz1))
      · exact False.elim (hne (hx.trans hy.symm))
  refine ⟨⟨_, hroot⟩, ?_⟩
  intro l hl m hm
  exact (hall l hl).trans (Relation.ReflTransGen.symmetric (fun _ _ => adj_symm) (hall m hm))

private def cycleLine {p q r : ℕ} : Line p q r → Line q r p
  | .pLine y z => .rLine y z
  | .qLine x z => .pLine z x
  | .rLine x y => .qLine y x

private def uncycleLine {p q r : ℕ} : Line q r p → Line p q r
  | .pLine z x => .qLine x z
  | .qLine y x => .rLine x y
  | .rLine y z => .pLine y z

private theorem connected_cycle {p q r : ℕ}
    (α : Fin p → Bool) (β : Fin q → Bool) (γ : Fin r → Bool)
    (h : Connected (mask β γ α)) : Connected (mask α β γ) := by
  classical
  have hmem : ∀ l : Line q r p,
      l ∈ mask β γ α ↔ uncycleLine l ∈ mask α β γ := by
    intro l; cases l <;> simp [mask, uncycleLine, ne_comm]
  have hback : ∀ l : Line p q r, uncycleLine (cycleLine l) = l := by
    intro l; cases l <;> rfl
  have hadj : ∀ {l m : Line q r p}, Adj (mask β γ α) l m →
      Adj (mask α β γ) (uncycleLine l) (uncycleLine m) := by
    intro l m ⟨hl, hm, ⟨y, z, x⟩, hls, hms⟩
    refine ⟨(hmem l).mp hl, (hmem m).mp hm, ⟨x, y, z⟩, ?_, ?_⟩
    · cases l <;> simpa [uncycleLine, covers, and_comm] using hls
    · cases m <;> simpa [uncycleLine, covers, and_comm] using hms
  have hpath : ∀ {l m : Line q r p}, Relation.ReflTransGen (Adj (mask β γ α)) l m →
      Relation.ReflTransGen (Adj (mask α β γ)) (uncycleLine l) (uncycleLine m) := by
    intro l m hp
    induction hp with
    | refl => exact .refl
    | tail _ he ih => exact ih.tail (hadj he)
  obtain ⟨l, hl⟩ := h.1
  refine ⟨⟨uncycleLine l, (hmem l).mp hl⟩, ?_⟩
  intro a ha b hb
  have ha' : cycleLine a ∈ mask β γ α :=
    (hmem _).mpr (by simpa only [hback] using ha)
  have hb' : cycleLine b ∈ mask β γ α :=
    (hmem _).mpr (by simpa only [hback] using hb)
  simpa only [hback] using hpath (h.2 _ ha' _ hb')

private def Mixed {n : ℕ} (f : Fin n → Bool) : Prop :=
  ∃ i j, f i = false ∧ f j = true

private theorem not_mixed_eq {n : ℕ} {f : Fin n → Bool} (h : ¬ Mixed f)
    (i j : Fin n) : f i = f j := by
  cases hi : f i <;> cases hj : f j
  · rfl
  · exact False.elim (h ⟨i, j, hi, hj⟩)
  · exact False.elim (h ⟨j, i, hj, hi⟩)
  · rfl

private theorem connected_mixed_third {p q r : ℕ}
    (α : Fin p → Bool) (β : Fin q → Bool) (γ : Fin r → Bool)
    (hR : ∃ x y, α x ≠ β y) (hγ : Mixed γ) : Connected (mask α β γ) := by
  classical
  obtain ⟨x, y, hxy⟩ := hR
  obtain ⟨z0, z1, hz0, hz1⟩ := hγ
  cases hx : α x
  · have hy : β y = true := by cases hy : β y <;> simp_all
    exact connected_of_backbone α β γ x y z0 z1 hx hy hz0 hz1
  · have hy : β y = false := by cases hy : β y <;> simp_all
    have hc := connected_of_backbone (fun x => !(α x)) (fun y => !(β y))
      (fun z => !(γ z)) x y z1 z0
      (by simp [hx]) (by simp [hy]) (by simp [hz1]) (by simp [hz0])
    have heq : mask (fun x => !(α x)) (fun y => !(β y)) (fun z => !(γ z)) =
        mask α β γ := by
      ext l
      cases l <;> simp [mask]
    simpa only [heq] using hc

/-- Presence of all three elements excludes the disconnected, repeated
binary slices. This is a geometric connectivity result, not a positivity
assumption about an unproved formula catalog. -/
theorem mask_connected {p q r : ℕ}
    (α : Fin p → Bool) (β : Fin q → Bool) (γ : Fin r → Bool)
    (hP : ∃ y z, β y ≠ γ z) (hQ : ∃ x z, α x ≠ γ z)
    (hR : ∃ x y, α x ≠ β y) : Connected (mask α β γ) := by
  classical
  by_cases hγ : Mixed γ
  · exact connected_mixed_third α β γ hR hγ
  by_cases hβ : Mixed β
  · apply connected_cycle α β γ
    apply connected_cycle β γ α
    exact connected_mixed_third γ α β (by
      obtain ⟨x, z, h⟩ := hQ
      exact ⟨z, x, Ne.symm h⟩) hβ
  have hα : Mixed α := by
    by_contra hn
    obtain ⟨yP, zP, hP⟩ := hP
    obtain ⟨xQ, zQ, hQ⟩ := hQ
    obtain ⟨xR, yR, hR⟩ := hR
    have hx := not_mixed_eq hn xR xQ
    have hy := not_mixed_eq hβ yR yP
    have hz := not_mixed_eq hγ zQ zP
    cases hax : α xQ <;> cases hby : β yP <;> cases hcz : γ zP <;> simp_all
  exact connected_cycle α β γ (connected_mixed_third β γ α hP hα)

theorem exists_bits_weight {n a : ℕ} (ha : a ≤ n) :
    ∃ f : Fin n → Bool, weight f = a := by
  classical
  obtain ⟨S, _, hcard⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n))) (n := a) (by simpa using ha)
  refine ⟨fun i => decide (i ∈ S), ?_⟩
  simpa [weight] using hcard

private theorem singleton_weight {n : ℕ} (i : Fin n) :
    weight (fun j => decide (j = i)) = 1 := by
  classical
  simp [weight, Finset.filter_eq']

private theorem false_weight (n : ℕ) : weight (fun _ : Fin n => false) = 0 := by
  simp [weight]

private theorem binary_connected {p q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (x0 : Fin p) : Connected (mask (fun x => decide (x = x0))
      (fun _ : Fin q => false) (fun _ : Fin r => false)) := by
  classical
  let α := fun x : Fin p => decide (x = x0)
  let S := mask α (fun _ : Fin q => false) (fun _ : Fin r => false)
  let y0 : Fin q := ⟨0, hq⟩
  let z0 : Fin r := ⟨0, hr⟩
  have hq0 : Line.qLine x0 z0 ∈ S := by simp [S, mask, α]
  have hr0 : Line.rLine x0 y0 ∈ S := by simp [S, mask, α]
  have hall : ∀ l ∈ S, Relation.ReflTransGen (Adj S) l (.qLine x0 z0) := by
    intro l hl
    cases l with
    | pLine y z => simp [S, mask] at hl
    | qLine x z =>
      have hx : x = x0 := by simpa [S, mask, α] using hl
      subst x
      exact (Relation.ReflTransGen.single (qr_adj hl hr0)).trans
        (Relation.ReflTransGen.single (adj_symm (qr_adj hq0 hr0)))
    | rLine x y =>
      have hx : x = x0 := by simpa [S, mask, α] using hl
      subst x
      exact Relation.ReflTransGen.single (adj_symm (qr_adj hq0 hl))
  refine ⟨⟨_, hq0⟩, ?_⟩
  intro l hl m hm
  exact (hall l hl).trans (Relation.ReflTransGen.symmetric (fun _ _ => adj_symm) (hall m hm))

private theorem binary_pq_grid {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    ∃ S : Finset (Line p q r), Paired S ∧ Connected S ∧
      counts S = UniversalSynthesis.binaryPQ p q := by
  let z0 : Fin r := ⟨0, hr⟩
  let γ := fun z => decide (z = z0)
  refine ⟨mask (fun _ : Fin p => false) (fun _ : Fin q => false) γ,
    mask_paired _ _ _, ?_, ?_⟩
  · apply connected_cycle
    apply connected_cycle
    exact binary_connected hp hq z0
  · rw [mask_counts, false_weight, false_weight, singleton_weight]
    ext i; fin_cases i <;> simp [UniversalSynthesis.parity, UniversalSynthesis.binaryPQ]

private theorem binary_pr_grid {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    ∃ S : Finset (Line p q r), Paired S ∧ Connected S ∧
      counts S = UniversalSynthesis.binaryPR p r := by
  let y0 : Fin q := ⟨0, hq⟩
  let β := fun y => decide (y = y0)
  refine ⟨mask (fun _ : Fin p => false) β (fun _ : Fin r => false),
    mask_paired _ _ _, ?_, ?_⟩
  · apply connected_cycle
    exact binary_connected hr hp y0
  · rw [mask_counts, false_weight, singleton_weight, false_weight]
    ext i; fin_cases i <;> simp [UniversalSynthesis.parity, UniversalSynthesis.binaryPR]

private theorem binary_qr_grid {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    ∃ S : Finset (Line p q r), Paired S ∧ Connected S ∧
      counts S = UniversalSynthesis.binaryQR q r := by
  let x0 : Fin p := ⟨0, hp⟩
  let α := fun x => decide (x = x0)
  refine ⟨mask α (fun _ : Fin q => false) (fun _ : Fin r => false),
    mask_paired _ _ _, binary_connected hq hr x0, ?_⟩
  rw [mask_counts, singleton_weight, false_weight, false_weight]
  ext i; fin_cases i <;> simp [UniversalSynthesis.parity, UniversalSynthesis.binaryQR]

theorem positive_parity_grid {p q r : ℕ} {a b c : ℤ}
    (ha : 0 ≤ a) (hap : a ≤ p) (hb : 0 ≤ b) (hbq : b ≤ q)
    (hc : 0 ≤ c) (hcr : c ≤ r)
    (hpos : ∀ i, 0 < UniversalSynthesis.parity p q r a b c i) :
    ∃ S : Finset (Line p q r), Paired S ∧ Connected S ∧
      counts S = UniversalSynthesis.parity p q r a b c := by
  classical
  obtain ⟨α, hα⟩ := exists_bits_weight (n := p) (a := a.toNat) (by omega)
  obtain ⟨β, hβ⟩ := exists_bits_weight (n := q) (a := b.toNat) (by omega)
  obtain ⟨γ, hγ⟩ := exists_bits_weight (n := r) (a := c.toNat) (by omega)
  have hcounts : counts (mask α β γ) = UniversalSynthesis.parity p q r a b c := by
    rw [mask_counts, hα, hβ, hγ, Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb,
      Int.toNat_of_nonneg hc]
  refine ⟨mask α β γ, mask_paired _ _ _, ?_, hcounts⟩
  apply mask_connected
  · obtain ⟨y, z, h⟩ := (count_p_pos _).mp (by rw [hcounts]; exact hpos 0)
    exact ⟨y, z, by simpa [mask] using h⟩
  · obtain ⟨x, z, h⟩ := (count_q_pos _).mp (by rw [hcounts]; exact hpos 1)
    exact ⟨x, z, by simpa [mask] using h⟩
  · obtain ⟨x, y, h⟩ := (count_r_pos _).mp (by rw [hcounts]; exact hpos 2)
    exact ⟨x, y, by simpa [mask] using h⟩

/-- Every non-dimer entry of the formula catalog has an explicitly
paired, connected finite coordinate-line realization. Dimers require
repeated lines and are realized directly as two identical original atoms. -/
theorem valid_grid_witness {p q r : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r)
    {f : UniversalSynthesis.Formula} (hf : UniversalSynthesis.Valid p q r f) :
    f ∈ [UniversalSynthesis.dimerP, UniversalSynthesis.dimerQ, UniversalSynthesis.dimerR] ∨
      ∃ S : Finset (Line p q r), Paired S ∧ Connected S ∧ counts S = f := by
  rcases hf with hf | ⟨a, b, c, ha, hap, hb, hbq, hc, hcr, hpos, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · left; simp
    · left; simp
    · left; simp
    · exact Or.inr (binary_pq_grid (by omega) (by omega) (by omega))
    · exact Or.inr (binary_pr_grid (by omega) (by omega) (by omega))
    · exact Or.inr (binary_qr_grid (by omega) (by omega) (by omega))
  · exact Or.inr (positive_parity_grid ha hap hb hbq hc hcr hpos)

end CyclicAtoms.PrimeGrid
