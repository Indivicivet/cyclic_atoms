import CyclicAtoms.GeometryWitness357

namespace CyclicAtoms.Geometry

open Chemistry

theorem multiplicity_pos {C : Config} {p : Nat} (hp : C.HasElement p) :
    0 < C.multiplicity p := by
  obtain ⟨i, hi⟩ := hp
  change 0 < (C.filter (fun a => a.p == p)).length
  apply List.length_pos_of_mem (a := C.get i)
  exact List.mem_filter.mpr ⟨List.get_mem C i, by simpa only [beq_iff_eq] using hi⟩

theorem configFormula_threeElements {C : Config}
    (h3 : C.HasElement 3) (h5 : C.HasElement 5) (h7 : C.HasElement 7) :
    threeElements (configFormula C) :=
  ⟨multiplicity_pos h3, multiplicity_pos h5, multiplicity_pos h7⟩

theorem hasElement_iff_multiplicity_pos (C : Config) (p : Nat) :
    C.HasElement p ↔ 0 < C.multiplicity p := by
  refine ⟨multiplicity_pos, ?_⟩
  intro hp
  obtain ⟨a, ha⟩ := List.length_pos_iff_exists_mem.mp hp
  obtain ⟨haC, hap⟩ := List.mem_filter.mp ha
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp haC
  exact ⟨i, by simpa only [beq_iff_eq] using hap⟩

theorem multiplicity_zero_of_other {C : Config} (hC : Elements357 C) (q : Nat)
    (h3 : q ≠ 3) (h5 : q ≠ 5) (h7 : q ≠ 7) : C.multiplicity q = 0 := by
  by_contra hz
  obtain ⟨i, hi⟩ := (hasElement_iff_multiplicity_pos C q).mpr (Nat.pos_of_ne_zero hz)
  have hc := hC i
  omega

theorem every_original_molecule_synthesizable_formula357 (C : Config)
    (hm : IsMolecule C) (hC : Elements357 C)
    (h3 : C.HasElement 3) (h5 : C.HasElement 5) (h7 : C.HasElement 7) (p : Fin 3) :
    Synthesizable formulas357 reactionTable357 (feedPair357 p) (configFormula C) := by
  obtain ⟨a, b, c, hf⟩ := original_molecule_parity_formula hm hC h3 h5 h7
  have hpos := configFormula_threeElements h3 h5 h7
  rw [hf] at hpos ⊢
  exact every_parity_formula_synthesizable357 p a b c hpos

theorem every_elements357_formula_synthesizable (C : Config)
    (hm : IsMolecule C) (hC : Elements357 C) (p : Fin 3) :
    Synthesizable formulas357 reactionTable357 (feedPair357 p) (configFormula C) := by
  obtain ⟨g⟩ := original_molecule_grid_alignment hC hm
  by_cases hinj : Function.Injective g.lines
  · obtain ⟨α, β, γ, hmask⟩ := g.parityMask_exists hm hinj
    have hf := g.formula hinj
    rw [hmask, parityMask_counts] at hf
    obtain ⟨a, b, c, habc⟩ := rawParityFormula_normalized
      ⟨weight α, by have := weight_le α; omega⟩
      ⟨weight β, by have := weight_le β; omega⟩
      ⟨weight γ, by have := weight_le γ; omega⟩
    have hcf : configFormula C = parityFormula a b c := hf.trans habc
    have hne : 0 < (parityFormula a b c).n3 ∨ 0 < (parityFormula a b c).n5 ∨
        0 < (parityFormula a b c).n7 := by
      let root : Fin C.length := ⟨0, hm.connected.1⟩
      rcases hC root with hr | hr | hr
      · left; exact hcf ▸ multiplicity_pos ⟨root, hr⟩
      · right; left; exact hcf ▸ multiplicity_pos ⟨root, hr⟩
      · right; right; exact hcf ▸ multiplicity_pos ⟨root, hr⟩
    have hz3 : (parityFormula a b c).n3 = 0 →
        (parityFormula a b c).n5 ≤ 7 ∧ (parityFormula a b c).n7 ≤ 5 := by
      intro h0
      have hm3 : C.multiplicity 3 = 0 := by rw [← hcf] at h0; exact h0
      simpa [← hcf, configFormula] using g.no_element_3_bounds hm hinj hm3
    have hz5 : (parityFormula a b c).n5 = 0 →
        (parityFormula a b c).n3 ≤ 7 ∧ (parityFormula a b c).n7 ≤ 3 := by
      intro h0
      have hm5 : C.multiplicity 5 = 0 := by rw [← hcf] at h0; exact h0
      simpa [← hcf, configFormula] using g.no_element_5_bounds hm hinj hm5
    have hz7 : (parityFormula a b c).n7 = 0 →
        (parityFormula a b c).n3 ≤ 5 ∧ (parityFormula a b c).n5 ≤ 3 := by
      intro h0
      have hm7 : C.multiplicity 7 = 0 := by rw [← hcf] at h0; exact h0
      simpa [← hcf, configFormula] using g.no_element_7_bounds hm hinj hm7
    rw [hcf]
    exact connected_parity_formula_synthesizable357 p a b c hne hz3 hz5 hz7
  · obtain ⟨i, j, hij, hne⟩ : ∃ i j : Fin C.length, g.lines i = g.lines j ∧ i ≠ j := by
      by_contra hall
      exact hinj fun i j hij => by_contra fun hne => hall ⟨i, j, hij, hne⟩
    have hsame : Atom.SamePoints (C.get i) (C.get j) := by
      intro x
      rw [g.points, g.points, hij]
    have htwo := identical_atoms_molecule_only_two hm hne hsame
    have hcard_univ : (Finset.univ : Finset (Fin C.length)).card = 2 := by
      have hu : (Finset.univ : Finset (Fin C.length)) = {i, j} := by
        ext k
        simp [htwo k]
      rw [hu, Finset.card_pair hne]
    have hmult : ∀ r : Nat, C.multiplicity r = if (C.get i).p = r then 2 else 0 := by
      intro r
      rw [Config.multiplicity, filter_length_eq_card]
      have halleq : ∀ k : Fin C.length, (C.get k).p = (C.get i).p := by
        intro k
        rcases htwo k with hk | hk
        · rw [hk]
        · rw [hk]; exact (g.element j).symm.trans (hij.symm ▸ g.element i)
      by_cases hr : (C.get i).p = r
      · have hfilt : Finset.univ.filter (fun k : Fin C.length => (C.get k).p == r) =
            Finset.univ := by
          ext k
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true,
            beq_iff_eq, ← List.get_eq_getElem] using (halleq k).trans hr
        rw [if_pos hr, hfilt, hcard_univ]
      · have hfilt : Finset.univ.filter (fun k : Fin C.length => (C.get k).p == r) = ∅ := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.not_mem_empty,
            iff_false, beq_iff_eq, ← List.get_eq_getElem]
          rw [halleq k]
          exact hr
        rw [if_neg hr, hfilt, Finset.card_empty]
    rcases hC i with h3 | h5 | h7
    · have hf : configFormula C = formula357 ⟨3, by decide⟩ := by
        unfold configFormula
        rw [hmult 3, hmult 5, hmult 7, h3]
        decide
      rw [hf]
      exact every_catalog_formula_synthesizable357 p ⟨3, by decide⟩
    · have hf : configFormula C = formula357 ⟨1, by decide⟩ := by
        unfold configFormula
        rw [hmult 3, hmult 5, hmult 7, h5]
        decide
      rw [hf]
      exact every_catalog_formula_synthesizable357 p ⟨1, by decide⟩
    · have hf : configFormula C = formula357 ⟨0, by decide⟩ := by
        unfold configFormula
        rw [hmult 3, hmult 5, hmult 7, h7]
        decide
      rw [hf]
      exact every_catalog_formula_synthesizable357 p ⟨0, by decide⟩

theorem formula_beq_true (a b : Formula) : (a == b) = true ↔ a = b := by
  cases a with
  | mk a3 a5 a7 =>
    cases b with
    | mk b3 b5 b7 =>
      change ((a3 == b3) && ((a5 == b5) && (a7 == b7))) = true ↔ _
      simp only [Bool.and_eq_true, beq_iff_eq, Formula.mk.injEq]

instance : LawfulBEq Formula where
  eq_of_beq := (formula_beq_true _ _).mp
  rfl := (formula_beq_true _ _).mpr rfl

/-- Every stock entry is an actual original molecule with the permitted elements. -/
structure Molecule357 where
  config : Config
  molecule : IsMolecule config
  elements : Elements357 config

def Molecule357.formula (m : Molecule357) : Formula := configFormula m.config

/-- A concerted 2→2 replacement, including arbitrary unchanged stock. -/
inductive MolecularStep : List Molecule357 → List Molecule357 → Prop where
  | replace (before inputs outputs rest : List Molecule357)
      (two : inputs.length = 2 ∧ outputs.length = 2)
      (conserved : inventory (inputs.map Molecule357.formula) =
        inventory (outputs.map Molecule357.formula))
      (reorder : before.Perm (inputs ++ rest)) :
      MolecularStep before (outputs ++ rest)

inductive MolecularChain : List Molecule357 → List Molecule357 → Prop where
  | refl (stock) : MolecularChain stock stock
  | step {a b c} : MolecularStep a b → MolecularChain b c → MolecularChain a c

def CanSynthesize (p : Fin 3) (target : Molecule357) : Prop :=
  ∃ initial final : List Molecule357,
    (∀ m ∈ initial, m.formula ∈ feedPair357 p) ∧
    MolecularChain initial final ∧ target ∈ final

def stockCount (stock : List Molecule357) (q : Nat) : Nat :=
  (stock.map (fun m => m.config.multiplicity q)).sum

theorem inventory_fields (side : List Formula) :
    inventory side = ⟨(side.map Formula.n3).sum, (side.map Formula.n5).sum,
      (side.map Formula.n7).sum⟩ := by
  have hf : ∀ (side : List Formula) (acc : Formula),
      side.foldl (fun total m =>
        Formula.mk (total.n3 + m.n3) (total.n5 + m.n5) (total.n7 + m.n7)) acc =
      ⟨acc.n3 + (side.map Formula.n3).sum, acc.n5 + (side.map Formula.n5).sum,
        acc.n7 + (side.map Formula.n7).sum⟩ := by
    intro side
    induction side with
    | nil => intro acc; cases acc; rfl
    | cons a side ih =>
      intro acc
      simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons]
      congr 1 <;> omega
  simpa only [inventory, Nat.zero_add] using hf side ⟨0, 0, 0⟩

theorem inventory_stock (stock : List Molecule357) :
    inventory (stock.map Molecule357.formula) =
      ⟨stockCount stock 3, stockCount stock 5, stockCount stock 7⟩ := by
  rw [inventory_fields]
  simp only [List.map_map, stockCount, Molecule357.formula, configFormula,
    Function.comp_def]

/-- The endpoint rule conserves every element, not just an unspecified invariant. -/
theorem MolecularStep.conserves {a b : List Molecule357} (h : MolecularStep a b) (q : Nat) :
    stockCount a q = stockCount b q := by
  cases h with
  | replace inputs outputs rest two hb hp =>
    have hperm : stockCount a q = stockCount (inputs ++ rest) q :=
      by simpa only [stockCount] using
        (hp.map (fun m : Molecule357 => m.config.multiplicity q)).sum_eq
    rw [hperm]
    simp only [stockCount, List.map_append, List.sum_append]
    apply congrArg (fun n => n + (rest.map (fun m => m.config.multiplicity q)).sum)
    change stockCount inputs q = stockCount outputs q
    rw [inventory_stock, inventory_stock] at hb
    by_cases h3 : q = 3
    · subst q; exact congrArg Formula.n3 hb
    by_cases h5 : q = 5
    · subst q; exact congrArg Formula.n5 hb
    by_cases h7 : q = 7
    · subst q; exact congrArg Formula.n7 hb
    have hz : ∀ stock : List Molecule357, stockCount stock q = 0 := by
      intro stock
      induction stock with
      | nil => rfl
      | cons m stock ih =>
        simp only [stockCount, List.map_cons, List.sum_cons] at ih ⊢
        rw [multiplicity_zero_of_other m.elements q h3 h5 h7, ih, Nat.zero_add]
    rw [hz, hz]

theorem MolecularChain.conserves {a b : List Molecule357} (h : MolecularChain a b) (q : Nat) :
    stockCount a q = stockCount b q := by
  induction h with
  | refl => rfl
  | step hs _ ih => exact (hs.conserves q).trans ih

noncomputable def catalogMolecule (m : Formula) (hm : m ∈ formulas357) : Molecule357 :=
  let h := catalog_realizable357 m hm
  ⟨Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2.1⟩

theorem catalogMolecule_formula (m : Formula) (hm : m ∈ formulas357) :
    (catalogMolecule m hm).formula = m :=
  (Classical.choose_spec (catalog_realizable357 m hm)).2.2

/-- Choose the requested geometric isomer whenever its formula is produced. -/
noncomputable def realizeFor (target : Molecule357) (m : Formula) : Molecule357 := by
  classical
  exact if h : m = target.formula then target
    else if hm : m ∈ formulas357 then catalogMolecule m hm
    else ⟨witnessConfig357 0, witness_isMolecule357 0, witness_elements357 0⟩

theorem realizeFor_formula (target : Molecule357) (m : Formula) (hm : m ∈ formulas357) :
    (realizeFor target m).formula = m := by
  classical
  by_cases ht : m = target.formula
  · simpa only [realizeFor, dif_pos ht] using ht.symm
  · simp only [realizeFor, dif_neg ht, dif_pos hm, catalogMolecule_formula]

theorem realizeFor_target (target : Molecule357) : realizeFor target target.formula = target := by
  simp [realizeFor]

theorem removeOne_perm {m : Formula} {stock remaining : List Formula}
    (h : removeOne m stock = some remaining) : stock.Perm (m :: remaining) := by
  induction stock generalizing remaining with
  | nil => simp [removeOne] at h
  | cons a stock ih =>
    by_cases hma : m = a
    · simp [removeOne, hma] at h
      subst remaining
      simpa only [hma] using (List.Perm.refl (a :: stock))
    · cases hr : removeOne m stock with
      | none => simp [removeOne, hma, hr] at h
      | some rest =>
        simp [removeOne, hma, hr] at h
        subst remaining
        exact ((ih hr).cons a).trans (.swap m a rest)

theorem consume_perm {inputs stock remaining : List Formula}
    (h : consume inputs stock = some remaining) : stock.Perm (inputs ++ remaining) := by
  induction inputs generalizing stock with
  | nil => simp [consume] at h; subst remaining; exact .refl _
  | cons m inputs ih =>
    cases hr : removeOne m stock with
    | none => simp [consume, hr] at h
    | some rest =>
      simp only [consume, hr] at h
      exact (removeOne_perm hr).trans ((ih h).cons m)

theorem mapped_formulas (f : Formula → Molecule357)
    (hf : ∀ m ∈ formulas357, (f m).formula = m)
    (side : List Formula) (hs : side.all formulas357.contains = true) :
    (side.map f).map Molecule357.formula = side := by
  induction side with
  | nil => rfl
  | cons a side ih =>
    have hs' := List.all_eq_true.mp hs
    have ha := hf a (List.contains_iff_mem.mp (hs' a (by simp)))
    have hrest : side.all formulas357.contains = true :=
      List.all_eq_true.mpr (fun m hm => hs' m (by simp [hm]))
    simp only [List.map_cons, ha, ih hrest]

theorem table_two_to_two (i : Nat) (r : Reaction) (hr : reactionTable357[i]? = some r) :
    r.inputs.length = 2 ∧ r.outputs.length = 2 := by
  exact of_decide_eq_true (List.all_eq_true.mp reactions_are_two_to_two357 r
    (List.mem_of_getElem? hr))

/-- A successful multiplicity-sensitive execution lifts to actual molecular stocks. -/
theorem execute_geometric (f : Formula → Molecule357)
    (hf : ∀ m ∈ formulas357, (f m).formula = m)
    (steps : List Nat) (stock final : List Formula)
    (h : execute formulas357 reactionTable357 steps stock = some final) :
    MolecularChain (stock.map f) (final.map f) := by
  induction steps generalizing stock with
  | nil => simp [execute] at h; subst final; exact .refl _
  | cons i steps ih =>
    cases hr : reactionTable357[i]? with
    | none => simp [execute, hr] at h
    | some r =>
      by_cases hv : validReaction formulas357 r = true
      · cases hc : consume r.inputs stock with
        | none => simp [execute, hr, hv, hc] at h
        | some remaining =>
          simp only [execute, hr, hv, ite_true, hc] at h
          have hvalid := hv
          simp only [validReaction, smallSide, Bool.and_eq_true, decide_eq_true_eq] at hvalid
          have hin : r.inputs.all formulas357.contains = true := by tauto
          have hout : r.outputs.all formulas357.contains = true := by tauto
          have hbalance : inventory r.inputs = inventory r.outputs := by tauto
          have hperm := (consume_perm hc).map f
          have hstep : MolecularStep (stock.map f) ((r.outputs ++ remaining).map f) := by
            rw [List.map_append]
            apply MolecularStep.replace _ (r.inputs.map f) (r.outputs.map f) (remaining.map f)
            · simpa using table_two_to_two i r hr
            · rw [mapped_formulas f hf _ hin, mapped_formulas f hf _ hout]
              exact hbalance
            · simpa only [List.map_append] using hperm
          exact .step hstep (ih _ h)
      · simp [execute, hr, hv] at h

theorem feed_pairs_in_catalog : ∀ p : Fin 3,
    (feedPair357 p).all formulas357.contains = true := by native_decide

theorem synthesis_geometric (p : Fin 3) (target : Molecule357)
    (h : Synthesizable formulas357 reactionTable357 (feedPair357 p) target.formula) :
    CanSynthesize p target := by
  obtain ⟨plan, hplan⟩ := h
  cases he : execute formulas357 reactionTable357 plan.steps plan.initial with
  | none => simp [checkPlan, he] at hplan
  | some final =>
    simp only [checkPlan, he, Bool.and_eq_true] at hplan
    refine ⟨plan.initial.map (realizeFor target), final.map (realizeFor target), ?_,
      execute_geometric _ (realizeFor_formula target) _ _ _ he, ?_⟩
    · intro m hm
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
      have hfeed : a ∈ feedPair357 p :=
        List.contains_iff_mem.mp (List.all_eq_true.mp hplan.1 a ha)
      have hcat : a ∈ formulas357 :=
        List.contains_iff_mem.mp (List.all_eq_true.mp (feed_pairs_in_catalog p) a hfeed)
      simpa only [realizeFor_formula target a hcat] using hfeed
    · exact List.mem_map.mpr ⟨target.formula, List.contains_iff_mem.mp hplan.2,
        realizeFor_target target⟩

/-- End-to-end theorem: only the original molecule and element-set hypotheses remain. -/
theorem every_original_molecule_synthesizable357 (C : Config)
    (hm : IsMolecule C) (hC : Elements357 C)
    (h3 : C.HasElement 3) (h5 : C.HasElement 5) (h7 : C.HasElement 7) (p : Fin 3) :
    CanSynthesize p ⟨C, hm, hC⟩ :=
  synthesis_geometric p ⟨C, hm, hC⟩
    (every_original_molecule_synthesizable_formula357 C hm hC h3 h5 h7 p)

/-- Main end-to-end theorem: any molecule using only elements from {3,5,7}
(1-, 2-, or 3-element) can be synthesized from any binary feed pair via 2→2 steps. -/
theorem every_molecule_with_elements357 (C : Config) (hm : IsMolecule C)
    (helements : ∀ q : Nat, C.HasElement q → q = 3 ∨ q = 5 ∨ q = 7) (p : Fin 3) :
    ∃ initial final : List Molecule357,
      (∀ m ∈ initial, m.formula ∈ feedPair357 p) ∧
      MolecularChain initial final ∧ ∃ m ∈ final, m.config = C := by
  have hC : Elements357 C := fun i => helements _ ⟨i, rfl⟩
  obtain ⟨initial, final, hi, hc, ht⟩ :=
    synthesis_geometric p ⟨C, hm, hC⟩ (every_elements357_formula_synthesizable C hm hC p)
  exact ⟨initial, final, hi, hc, ⟨⟨C, hm, hC⟩, ht, rfl⟩⟩

/-- Corollary when all three elements {3,5,7} occur in `C`. -/
theorem every_molecule_with_exact_elements357 (C : Config) (hm : IsMolecule C)
    (helements : ∀ q : Nat, C.HasElement q ↔ q = 3 ∨ q = 5 ∨ q = 7) (p : Fin 3) :
    ∃ initial final : List Molecule357,
      (∀ m ∈ initial, m.formula ∈ feedPair357 p) ∧
      MolecularChain initial final ∧ ∃ m ∈ final, m.config = C :=
  every_molecule_with_elements357 C hm (fun q hq => (helements q).mp hq) p

/-- info: 'CyclicAtoms.Geometry.every_molecule_with_elements357' depends on axioms:
[propext, Classical.choice, Lean.ofReduceBool, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms every_molecule_with_elements357

/-- info: 'CyclicAtoms.Geometry.every_original_molecule_synthesizable357' depends on axioms:
[propext, Classical.choice, Lean.ofReduceBool, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms every_original_molecule_synthesizable357

/-- info: 'CyclicAtoms.Geometry.every_molecule_with_exact_elements357' depends on axioms:
[propext, Classical.choice, Lean.ofReduceBool, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms every_molecule_with_exact_elements357

end CyclicAtoms.Geometry
