import CyclicAtoms.GridAlignment
import CyclicAtoms.Chemistry357

namespace CyclicAtoms.Geometry

open Chemistry
open scoped BigOperators

def configFormula (C : Config) : Formula :=
  ⟨C.multiplicity 3, C.multiplicity 5, C.multiplicity 7⟩

/-- Count list entries through their indices, retaining repeated entries. -/
theorem filter_length_eq_card {α : Type} (l : List α) (p : α → Bool) :
    (l.filter p).length =
      (Finset.univ.filter (fun i : Fin l.length => p (l.get i) = true)).card := by
  have hs : ∀ l : List α, (l.filter p).length =
      (l.map (fun a => if p a then 1 else 0)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => cases h : p a <;> simp [h, ih, Nat.add_comm]
  calc
    (l.filter p).length = (l.map (fun a => if p a then 1 else 0)).sum := hs l
    _ = (List.ofFn (fun i : Fin l.length => if p (l.get i) then 1 else 0)).sum := by
      congr 1
      simpa only [List.ofFn_get, Function.comp_def] using
        (List.map_ofFn l.get (fun a => if p a then 1 else 0))
    _ = ∑ i : Fin l.length, if p (l.get i) then 1 else 0 := List.sum_ofFn
    _ = (Finset.univ.filter (fun i : Fin l.length => p (l.get i) = true)).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]

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

end CyclicAtoms.Geometry
