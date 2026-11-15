import CyclicAtoms.PrimeGeometry
import CyclicAtoms.ElementCounting
import CyclicAtoms.PrimeGridClassification

namespace CyclicAtoms.PrimeGeometry.Parameters

open Geometry PrimeGrid

noncomputable def Alignment.lineSet {t : Parameters} {C : Config} (g : Alignment t C) :
    Finset (Line t.p t.q t.r) := by
  classical
  exact Finset.univ.image g.lines

theorem Alignment.mem_lineSet {t : Parameters} {C : Config} (g : Alignment t C)
    (l : Line t.p t.q t.r) : l ∈ g.lineSet ↔ ∃ i, g.lines i = l := by
  classical
  simp [Alignment.lineSet]

theorem Alignment.bond_site {t : Parameters} {C : Config} (g : Alignment t C)
    {i j : Fin C.length} (h : BondAdj C i j) :
    ∃ s : Site t.p t.q t.r, covers (g.lines i) s ∧ covers (g.lines j) s := by
  obtain ⟨x, _, hi, hj⟩ := h
  obtain ⟨s, hs, hxs⟩ := (g.points i x).mp hi
  obtain ⟨u, hu, hxu⟩ := (g.points j x).mp hj
  have hsu : s = u := by
    apply ZMod.toAddCircle_injective t.N
    exact add_left_cancel (hxs.symm.trans hxu)
  exact ⟨t.coordinates s, hs, hsu ▸ hu⟩

theorem Alignment.connected {t : Parameters} {C : Config} (g : Alignment t C)
    (hm : IsMolecule C) : Connected g.lineSet := by
  classical
  let root : Fin C.length := ⟨0, hm.connected.1⟩
  refine ⟨⟨g.lines root, (g.mem_lineSet _).mpr ⟨root, rfl⟩⟩, ?_⟩
  intro l hl m hm'
  obtain ⟨i, rfl⟩ := (g.mem_lineSet l).mp hl
  obtain ⟨j, rfl⟩ := (g.mem_lineSet m).mp hm'
  have h := hm.connected.2 i j
  induction h with
  | refl i => exact .refl
  | @step i j k hij _ ih =>
    exact (ih ((g.mem_lineSet _).mpr ⟨j, rfl⟩)
      ((g.mem_lineSet _).mpr ⟨k, rfl⟩)).head ⟨(g.mem_lineSet _).mpr ⟨i, rfl⟩,
      (g.mem_lineSet _).mpr ⟨j, rfl⟩, g.bond_site hij⟩

theorem Alignment.paired {t : Parameters} {C : Config} (g : Alignment t C)
    (hm : IsMolecule C) (hinj : Function.Injective g.lines) : Paired g.lineSet := by
  classical
  intro site
  let s := t.coordinates.symm site
  let I := Finset.univ.filter (fun i : Fin C.length => covers (g.lines i) site)
  have himage : I.image g.lines = g.lineSet.filter (fun l => covers l site) := by
    ext l
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      g.mem_lineSet]
    aesop
  rw [← himage, Finset.card_image_of_injective _ hinj]
  by_cases hz : I = ∅
  · left; rw [hz]; rfl
  · right
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hz
    have hi' : (C.get i).hasPoint (t.sample g.origin s) := by
      apply (g.at_sample i s).mpr
      simpa [I, s] using hi
    obtain ⟨j, hij, hj, huniq⟩ := hm.paired i _ hi'
    have hI : I = {i, j} := by
      ext k
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hk
        apply huniq k
        apply (g.at_sample k s).mpr
        simpa [I, s] using hk
      · intro hk
        have hpoint : (C.get k).hasPoint (t.sample g.origin s) := by
          rcases hk with rfl | rfl
          · exact hi'
          · exact hj
        have hc := (g.at_sample k s).mp hpoint
        simpa [I, s] using hc
    rw [hI, Finset.card_pair hij]

theorem Alignment.multiplicity {t : Parameters} {C : Config} (g : Alignment t C)
    (hinj : Function.Injective g.lines) (e : ℕ) :
    C.multiplicity e = (g.lineSet.filter (fun l => element l = e)).card := by
  classical
  rw [Config.multiplicity, filter_length_eq_card]
  simp only [beq_iff_eq]
  have himage : (Finset.univ.filter (fun i : Fin C.length => (C.get i).p = e)).image g.lines =
      g.lineSet.filter (fun l => element l = e) := by
    ext l
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      g.mem_lineSet]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, rfl⟩, (g.element_eq i).trans hi⟩
    · rintro ⟨⟨i, rfl⟩, hi⟩
      exact ⟨i, (g.element_eq i).symm.trans hi, rfl⟩
  rw [← himage, Finset.card_image_of_injective _ hinj]

theorem Alignment.counts {t : Parameters} {C : Config} (g : Alignment t C)
    (hinj : Function.Injective g.lines) :
    counts g.lineSet = ![(C.multiplicity t.p : ℤ), C.multiplicity t.q, C.multiplicity t.r] := by
  classical
  ext i
  fin_cases i
  · change PrimeGrid.counts g.lineSet 0 = (C.multiplicity t.p : ℤ)
    rw [PrimeGrid.counts_p]
    apply congrArg (fun n : ℕ => (n : ℤ))
    calc
      _ = (g.lineSet.filter (fun l => element l = t.p)).card := by
        congr 1
        ext l
        cases l <;> simp [element, t.pq.symm, t.pr.symm]
      _ = C.multiplicity t.p := (g.multiplicity hinj t.p).symm
  · change PrimeGrid.counts g.lineSet 1 = (C.multiplicity t.q : ℤ)
    rw [PrimeGrid.counts_q]
    apply congrArg (fun n : ℕ => (n : ℤ))
    calc
      _ = (g.lineSet.filter (fun l => element l = t.q)).card := by
        congr 1
        ext l
        cases l <;> simp [element, t.pq, t.qr.symm]
      _ = C.multiplicity t.q := (g.multiplicity hinj t.q).symm
  · change PrimeGrid.counts g.lineSet 2 = (C.multiplicity t.r : ℤ)
    rw [PrimeGrid.counts_r]
    apply congrArg (fun n : ℕ => (n : ℤ))
    calc
      _ = (g.lineSet.filter (fun l => element l = t.r)).card := by
        congr 1
        ext l
        cases l <;> simp [element, t.pr, t.qr]
      _ = C.multiplicity t.r := (g.multiplicity hinj t.r).symm

/-- The noninjective case is an actual isolated two-atom dimer, not a
repeated-line configuration being silently treated as a finite set. -/
theorem Alignment.dimer_of_not_injective {t : Parameters} {C : Config} (g : Alignment t C)
    (hm : IsMolecule C) (hC : t.Elements C) (hinj : ¬ Function.Injective g.lines) :
    ![(C.multiplicity t.p : ℤ), C.multiplicity t.q, C.multiplicity t.r] ∈
      [UniversalSynthesis.dimerP, UniversalSynthesis.dimerQ, UniversalSynthesis.dimerR] := by
  classical
  obtain ⟨i, j, hij, hne⟩ : ∃ i j : Fin C.length, g.lines i = g.lines j ∧ i ≠ j := by
    by_contra hall
    exact hinj fun i j hij => by_contra fun hne => hall ⟨i, j, hij, hne⟩
  have hs : Atom.SamePoints (C.get i) (C.get j) := by
    intro x
    rw [g.points, g.points, hij]
  have htwo := identical_atoms_molecule_only_two hm hne hs
  have hcard : (Finset.univ : Finset (Fin C.length)).card = 2 := by
    have hu : (Finset.univ : Finset (Fin C.length)) = {i, j} := by
      ext k
      simp [htwo k]
    rw [hu, Finset.card_pair hne]
  have hall : ∀ k : Fin C.length, (C.get k).p = (C.get i).p := by
    intro k
    rcases htwo k with hk | hk
    · rw [hk]
    · rw [hk]; exact (g.element_eq j).symm.trans (hij.symm ▸ g.element_eq i)
  have hmult : ∀ e : ℕ, C.multiplicity e = if (C.get i).p = e then 2 else 0 := by
    intro e
    rw [Config.multiplicity, filter_length_eq_card]
    by_cases he : (C.get i).p = e
    · have hfilt : Finset.univ.filter (fun k : Fin C.length => (C.get k).p == e) =
          Finset.univ := by
        ext k
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true,
          beq_iff_eq, ← List.get_eq_getElem] using (hall k).trans he
      rw [if_pos he, hfilt, hcard]
    · have hfilt : Finset.univ.filter (fun k : Fin C.length => (C.get k).p == e) = ∅ := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.not_mem_empty,
          iff_false, beq_iff_eq, ← List.get_eq_getElem]
        rw [hall k]
        exact he
      rw [if_neg he, hfilt, Finset.card_empty]
  rcases hC i with hp | hq | hr
  · have hf : ![(C.multiplicity t.p : ℤ), C.multiplicity t.q, C.multiplicity t.r] =
        UniversalSynthesis.dimerP := by
      rw [hmult t.p, hmult t.q, hmult t.r, hp]
      simp [t.pq, t.pr, UniversalSynthesis.dimerP]
    simp [hf]
  · have hf : ![(C.multiplicity t.p : ℤ), C.multiplicity t.q, C.multiplicity t.r] =
        UniversalSynthesis.dimerQ := by
      rw [hmult t.p, hmult t.q, hmult t.r, hq]
      simp [t.pq.symm, t.qr, UniversalSynthesis.dimerQ]
    simp [hf]
  · have hf : ![(C.multiplicity t.p : ℤ), C.multiplicity t.q, C.multiplicity t.r] =
        UniversalSynthesis.dimerR := by
      rw [hmult t.p, hmult t.q, hmult t.r, hr]
      simp [t.pr.symm, t.qr.symm, UniversalSynthesis.dimerR]
    simp [hf]

/-- Classification starts from the original geometric molecule predicate. -/
theorem original_molecule_valid (t : Parameters) (C : Config)
    (hm : IsMolecule C) (hC : t.Elements C) :
    UniversalSynthesis.Valid t.p t.q t.r
      ![(C.multiplicity t.p : ℤ), C.multiplicity t.q, C.multiplicity t.r] := by
  classical
  obtain ⟨g⟩ := t.molecule_alignment hC hm
  by_cases hinj : Function.Injective g.lines
  · rw [← g.counts hinj]
    exact valid_of_paired_connected t.primeP.pos t.primeQ.pos t.primeR.pos
      (g.paired hm hinj) (g.connected hm)
  · apply Or.inl
    have hd := g.dimer_of_not_injective hm hC hinj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
    tauto

end CyclicAtoms.PrimeGeometry.Parameters
