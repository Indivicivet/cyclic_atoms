import CyclicAtoms.GridAlignment
import CyclicAtoms.Chemistry357
import CyclicAtoms.ElementCounting

namespace CyclicAtoms.Geometry

open Chemistry
open scoped BigOperators

def configFormula (C : Config) : Formula :=
  ⟨C.multiplicity 3, C.multiplicity 5, C.multiplicity 7⟩

def lineCount (m : Line → Bool) : Formula :=
  ⟨(Finset.univ.filter (fun l => lineElement l = 3 ∧ m l = true)).card,
   (Finset.univ.filter (fun l => lineElement l = 5 ∧ m l = true)).card,
   (Finset.univ.filter (fun l => lineElement l = 7 ∧ m l = true)).card⟩

theorem GridAlignment.count {C : Config} (g : GridAlignment C)
    (hinj : Function.Injective g.lines) (p : Nat) :
    C.multiplicity p =
      (Finset.univ.filter (fun l => lineElement l = p ∧ g.present l = true)).card := by
  classical
  rw [Config.multiplicity, filter_length_eq_card]
  simp only [beq_iff_eq]
  have himage : (Finset.univ.filter (fun i : Fin C.length => (C.get i).p = p)).image g.lines =
      Finset.univ.filter (fun l => lineElement l = p ∧ g.present l = true) := by
    ext l
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(g.element i).trans hi, (g.present_iff _).mpr ⟨i, rfl⟩⟩
    · rintro ⟨hl, hpres⟩
      obtain ⟨i, rfl⟩ := (g.present_iff l).mp hpres
      exact ⟨i, (g.element i).symm.trans hl, rfl⟩
  rw [← himage, Finset.card_image_of_injective _ hinj]

theorem GridAlignment.formula {C : Config} (g : GridAlignment C)
    (hinj : Function.Injective g.lines) : configFormula C = lineCount g.present := by
  unfold configFormula lineCount
  rw [g.count hinj 3, g.count hinj 5, g.count hinj 7]

def lineX (l : Line) : Fin 3 := ⟨lineOffset l % 3, Nat.mod_lt _ (by decide)⟩
def lineY (l : Line) : Fin 5 := ⟨lineOffset l % 5, Nat.mod_lt _ (by decide)⟩
def lineZ (l : Line) : Fin 7 := ⟨lineOffset l % 7, Nat.mod_lt _ (by decide)⟩

theorem line_reconstruct : ∀ l : Line,
    l = if lineElement l = 3 then aLine (lineY l) (lineZ l)
        else if lineElement l = 5 then bLine (lineX l) (lineZ l)
        else cLine (lineX l) (lineY l) := by native_decide

def parityMask (α : Fin 3 → Bool) (β : Fin 5 → Bool) (γ : Fin 7 → Bool)
    (l : Line) : Bool :=
  if lineElement l = 3 then bitXor (β (lineY l)) (γ (lineZ l))
  else if lineElement l = 5 then bitXor (α (lineX l)) (γ (lineZ l))
  else bitXor (α (lineX l)) (β (lineY l))

def weight {n : Nat} (f : Fin n → Bool) : Nat :=
  (Finset.univ.filter (fun i => f i = true)).card

def rawParityFormula (a b c : Nat) : Formula :=
  ⟨b * (7 - c) + (5 - b) * c,
   a * (7 - c) + (3 - a) * c,
   a * (5 - b) + (3 - a) * b⟩

/-- Exact counting for every bit assignment, not a sampled set of geometries. -/
theorem parityMask_counts : ∀ (α : Fin 3 → Bool) (β : Fin 5 → Bool) (γ : Fin 7 → Bool),
    lineCount (parityMask α β γ) = rawParityFormula (weight α) (weight β) (weight γ) := by
  native_decide

theorem weight_le {n : Nat} (f : Fin n → Bool) : weight f ≤ n := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_fin n)

theorem rawParityFormula_normalized : ∀ (a : Fin 4) (b : Fin 6) (c : Fin 8),
    ∃ a' : Fin 2, ∃ b' : Fin 6, ∃ c' : Fin 8,
      rawParityFormula a.val b.val c.val = parityFormula a' b' c' := by native_decide

theorem GridAlignment.parityMask_exists {C : Config} (g : GridAlignment C)
    (hm : IsMolecule C) (hinj : Function.Injective g.lines) :
    ∃ α β γ, g.present = parityMask α β γ := by
  obtain ⟨α, β, γ, hA, hB, hC⟩ := parity_factorization (0 : Fin 3) (0 : Fin 5) (0 : Fin 7)
    (fun y z => g.present (aLine y z)) (fun x z => g.present (bLine x z))
    (fun x y => g.present (cLine x y)) (g.parity hm hinj)
  refine ⟨α, β, γ, ?_⟩
  funext l
  have hl := line_reconstruct l
  unfold parityMask
  split_ifs with h3 h5
  · simp only [h3, if_true] at hl
    exact (congrArg g.present hl).trans (hA _ _)
  · simp only [h3, if_false, h5, if_true] at hl
    exact (congrArg g.present hl).trans (hB _ _)
  · simp only [h3, if_false, h5] at hl
    exact (congrArg g.present hl).trans (hC _ _)

/-- The missing classification bridge, with only original geometric hypotheses. -/
theorem original_molecule_parity_formula {C : Config} (hm : IsMolecule C)
    (hC : Elements357 C) (h3 : C.HasElement 3) (h5 : C.HasElement 5)
    (h7 : C.HasElement 7) :
    ∃ a : Fin 2, ∃ b : Fin 6, ∃ c : Fin 8, configFormula C = parityFormula a b c := by
  obtain ⟨g⟩ := original_molecule_grid_alignment hC hm
  have hinj := g.injective hm h3 h5 h7
  obtain ⟨α, β, γ, hmask⟩ := g.parityMask_exists hm hinj
  have hf := g.formula hinj
  rw [hmask, parityMask_counts] at hf
  obtain ⟨a, b, c, habc⟩ := rawParityFormula_normalized
    ⟨weight α, by have := weight_le α; omega⟩
    ⟨weight β, by have := weight_le β; omega⟩
    ⟨weight γ, by have := weight_le γ; omega⟩
  exact ⟨a, b, c, hf.trans habc⟩

theorem lineX_of_covers : ∀ (l : Line) (x : Fin 3) (y : Fin 5) (z : Fin 7),
    lineElement l ≠ 3 → covers l (site x y z) = true → lineX l = x := by native_decide

theorem lineY_of_covers : ∀ (l : Line) (x : Fin 3) (y : Fin 5) (z : Fin 7),
    lineElement l ≠ 5 → covers l (site x y z) = true → lineY l = y := by native_decide

theorem lineZ_of_covers : ∀ (l : Line) (x : Fin 3) (y : Fin 5) (z : Fin 7),
    lineElement l ≠ 7 → covers l (site x y z) = true → lineZ l = z := by native_decide

theorem sliceX_card_5 : ∀ x : Fin 3,
    (Finset.univ.filter (fun l => lineElement l = 5 ∧ lineX l = x)).card ≤ 7 := by native_decide

theorem sliceX_card_7 : ∀ x : Fin 3,
    (Finset.univ.filter (fun l => lineElement l = 7 ∧ lineX l = x)).card ≤ 5 := by native_decide

theorem sliceY_card_3 : ∀ y : Fin 5,
    (Finset.univ.filter (fun l => lineElement l = 3 ∧ lineY l = y)).card ≤ 7 := by native_decide

theorem sliceY_card_7 : ∀ y : Fin 5,
    (Finset.univ.filter (fun l => lineElement l = 7 ∧ lineY l = y)).card ≤ 3 := by native_decide

theorem sliceZ_card_3 : ∀ z : Fin 7,
    (Finset.univ.filter (fun l => lineElement l = 3 ∧ lineZ l = z)).card ≤ 5 := by native_decide

theorem sliceZ_card_5 : ∀ z : Fin 7,
    (Finset.univ.filter (fun l => lineElement l = 5 ∧ lineZ l = z)).card ≤ 3 := by native_decide

theorem GridAlignment.bond_site {C : Config} (g : GridAlignment C)
    {u v : Fin C.length} (h : BondAdj C u v) :
    ∃ x : Fin 3, ∃ y : Fin 5, ∃ z : Fin 7,
      covers (g.lines u) (site x y z) = true ∧ covers (g.lines v) (site x y z) = true := by
  obtain ⟨w, _, hu, hv⟩ := h
  obtain ⟨s, hus, hw⟩ := (g.points u w).mp hu
  obtain ⟨t, hvt, hwt⟩ := (g.points v w).mp hv
  rw [hw, add_left_cancel_iff] at hwt
  have hst := ZMod.toAddCircle_injective 105 hwt
  rw [← hst] at hvt
  obtain ⟨x, y, z, rfl⟩ := site_surjective s
  exact ⟨x, y, z, hus, hvt⟩

theorem GridAlignment.slice_const {C : Config} (g : GridAlignment C)
    {α : Type} (coord : Line → α) (hc : IsConnected C)
    (hstep : ∀ u v : Fin C.length, BondAdj C u v → coord (g.lines u) = coord (g.lines v)) :
    ∃ c : α, ∀ i : Fin C.length, coord (g.lines i) = c := by
  let root : Fin C.length := ⟨0, hc.1⟩
  refine ⟨coord (g.lines root), fun i => ?_⟩
  have hwalk := hc.2 root i
  suffices ∀ {u v : Fin C.length}, BondReachable C u v →
      coord (g.lines u) = coord (g.lines v) from (this hwalk).symm
  intro u v huv
  induction huv with
  | refl => rfl
  | step hab _ ih => exact (hstep _ _ hab).trans ih

theorem GridAlignment.no_element_3_bounds {C : Config} (g : GridAlignment C)
    (hm : IsMolecule C) (hinj : Function.Injective g.lines) (h0 : C.multiplicity 3 = 0) :
    C.multiplicity 5 ≤ 7 ∧ C.multiplicity 7 ≤ 5 := by
  have hno3 : ∀ k : Fin C.length, lineElement (g.lines k) ≠ 3 := by
    intro k hk
    have hmem : C.get k ∈ C.filter (fun a => a.p == 3) :=
      List.mem_filter.mpr ⟨List.get_mem C k, by
        simpa only [List.get_eq_getElem, beq_iff_eq] using (g.element k).symm.trans hk⟩
    have hpos := List.length_pos_of_mem hmem
    change 0 < C.multiplicity 3 at hpos
    omega
  obtain ⟨x0, hx0⟩ := g.slice_const lineX hm.connected fun u v huv => by
    obtain ⟨x, y, z, hu, hv⟩ := g.bond_site huv
    exact (lineX_of_covers _ x y z (hno3 u) hu).trans (lineX_of_covers _ x y z (hno3 v) hv).symm
  have hbound : ∀ (e : Nat) (n : Nat),
      (Finset.univ.filter (fun l => lineElement l = e ∧ lineX l = x0)).card ≤ n →
      C.multiplicity e ≤ n := by
    intro e n hn
    rw [g.count hinj e]
    refine le_trans (Finset.card_le_card ?_) hn
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    obtain ⟨i, rfl⟩ := (g.present_iff l).mp hl.2
    exact ⟨hl.1, hx0 i⟩
  exact ⟨hbound 5 7 (sliceX_card_5 x0), hbound 7 5 (sliceX_card_7 x0)⟩

theorem GridAlignment.no_element_5_bounds {C : Config} (g : GridAlignment C)
    (hm : IsMolecule C) (hinj : Function.Injective g.lines) (h0 : C.multiplicity 5 = 0) :
    C.multiplicity 3 ≤ 7 ∧ C.multiplicity 7 ≤ 3 := by
  have hno5 : ∀ k : Fin C.length, lineElement (g.lines k) ≠ 5 := by
    intro k hk
    have hmem : C.get k ∈ C.filter (fun a => a.p == 5) :=
      List.mem_filter.mpr ⟨List.get_mem C k, by
        simpa only [List.get_eq_getElem, beq_iff_eq] using (g.element k).symm.trans hk⟩
    have hpos := List.length_pos_of_mem hmem
    change 0 < C.multiplicity 5 at hpos
    omega
  obtain ⟨y0, hy0⟩ := g.slice_const lineY hm.connected fun u v huv => by
    obtain ⟨x, y, z, hu, hv⟩ := g.bond_site huv
    exact (lineY_of_covers _ x y z (hno5 u) hu).trans (lineY_of_covers _ x y z (hno5 v) hv).symm
  have hbound : ∀ (e : Nat) (n : Nat),
      (Finset.univ.filter (fun l => lineElement l = e ∧ lineY l = y0)).card ≤ n →
      C.multiplicity e ≤ n := by
    intro e n hn
    rw [g.count hinj e]
    refine le_trans (Finset.card_le_card ?_) hn
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    obtain ⟨i, rfl⟩ := (g.present_iff l).mp hl.2
    exact ⟨hl.1, hy0 i⟩
  exact ⟨hbound 3 7 (sliceY_card_3 y0), hbound 7 3 (sliceY_card_7 y0)⟩

theorem GridAlignment.no_element_7_bounds {C : Config} (g : GridAlignment C)
    (hm : IsMolecule C) (hinj : Function.Injective g.lines) (h0 : C.multiplicity 7 = 0) :
    C.multiplicity 3 ≤ 5 ∧ C.multiplicity 5 ≤ 3 := by
  have hno7 : ∀ k : Fin C.length, lineElement (g.lines k) ≠ 7 := by
    intro k hk
    have hmem : C.get k ∈ C.filter (fun a => a.p == 7) :=
      List.mem_filter.mpr ⟨List.get_mem C k, by
        simpa only [List.get_eq_getElem, beq_iff_eq] using (g.element k).symm.trans hk⟩
    have hpos := List.length_pos_of_mem hmem
    change 0 < C.multiplicity 7 at hpos
    omega
  obtain ⟨z0, hz0⟩ := g.slice_const lineZ hm.connected fun u v huv => by
    obtain ⟨x, y, z, hu, hv⟩ := g.bond_site huv
    exact (lineZ_of_covers _ x y z (hno7 u) hu).trans (lineZ_of_covers _ x y z (hno7 v) hv).symm
  have hbound : ∀ (e : Nat) (n : Nat),
      (Finset.univ.filter (fun l => lineElement l = e ∧ lineZ l = z0)).card ≤ n →
      C.multiplicity e ≤ n := by
    intro e n hn
    rw [g.count hinj e]
    refine le_trans (Finset.card_le_card ?_) hn
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    obtain ⟨i, rfl⟩ := (g.present_iff l).mp hl.2
    exact ⟨hl.1, hz0 i⟩
  exact ⟨hbound 3 5 (sliceZ_card_3 z0), hbound 5 3 (sliceZ_card_5 z0)⟩

end CyclicAtoms.Geometry
