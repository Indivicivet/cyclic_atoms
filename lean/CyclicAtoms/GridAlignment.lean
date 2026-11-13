import CyclicAtoms.GridLines
import CyclicAtoms.Elementary

namespace CyclicAtoms.Geometry

open Chemistry

structure GridAlignment (C : Config) where
  origin : Phase
  lines : Fin C.length → Line
  element : ∀ i, lineElement (lines i) = (C.get i).p
  points : ∀ i x, (C.get i).hasPoint x ↔ ∃ s : ZMod 105,
    covers (lines i) s = true ∧ circle x = circle origin + grid s

theorem original_molecule_grid_alignment {C : Config} (hC : Elements357 C)
    (hm : IsMolecule C) : Nonempty (GridAlignment C) := by
  obtain ⟨θ, hθ⟩ := connected_grid_alignment hC hm.connected
  choose k hk using hθ
  exact ⟨{
    origin := θ
    lines := fun i => lineFor (C.get i).p (k i)
    element := fun i => lineFor_element _ (hC i) _
    points := fun i x => aligned_atom_hasPoint _ (hC i) θ (k i) (hk i) x
  }⟩

theorem GridAlignment.sample {C : Config} (g : GridAlignment C)
    (i : Fin C.length) (s : ZMod 105) :
    (C.get i).hasPoint (gridPoint g.origin s) ↔ covers (g.lines i) s = true := by
  rw [g.points]
  constructor
  · rintro ⟨t, ht, heq⟩
    rw [circle_gridPoint, add_left_cancel_iff] at heq
    have hst := ZMod.toAddCircle_injective 105 heq
    simpa [hst] using ht
  · intro hs
    exact ⟨s, hs, circle_gridPoint g.origin s⟩

/-- Three different elements exclude the isolated identical-atom dimer case. -/
theorem GridAlignment.injective {C : Config} (g : GridAlignment C)
    (hm : IsMolecule C) (h3 : C.HasElement 3) (h5 : C.HasElement 5)
    (h7 : C.HasElement 7) : Function.Injective g.lines := by
  intro i j hij
  by_contra hne
  have hs : Atom.SamePoints (C.get i) (C.get j) := by
    intro x
    rw [g.points, g.points, hij]
  have htwo := identical_atoms_molecule_only_two hm hne hs
  obtain ⟨i3, h3⟩ := h3
  obtain ⟨i5, h5⟩ := h5
  obtain ⟨i7, h7⟩ := h7
  rcases htwo i3 with hi3 | hi3 <;>
    rcases htwo i5 with hi5 | hi5 <;>
    rcases htwo i7 with hi7 | hi7 <;>
    subst_vars <;> omega

def GridAlignment.present {C : Config} (g : GridAlignment C) (l : Line) : Bool :=
  decide (∃ i, g.lines i = l)

theorem GridAlignment.present_iff {C : Config} (g : GridAlignment C) (l : Line) :
    g.present l = true ↔ ∃ i, g.lines i = l := by simp [GridAlignment.present]

theorem GridAlignment.present_partner {C : Config} (g : GridAlignment C)
    (hm : IsMolecule C) (hinj : Function.Injective g.lines) (s : ZMod 105)
    (l : Line) (hl : g.present l = true) (hs : covers l s = true) :
    ∃ m : Line, m ≠ l ∧ g.present m = true ∧ covers m s = true ∧
      ∀ n : Line, g.present n = true → covers n s = true → n = l ∨ n = m := by
  obtain ⟨i, rfl⟩ := (g.present_iff l).mp hl
  obtain ⟨j, hij, hj, hunique⟩ := hm.paired i (gridPoint g.origin s) ((g.sample i s).mpr hs)
  refine ⟨g.lines j, (fun heq => hij (hinj heq.symm)),
    (g.present_iff _).mpr ⟨j, rfl⟩, (g.sample j s).mp hj, ?_⟩
  intro n hn hns
  obtain ⟨k, rfl⟩ := (g.present_iff n).mp hn
  rcases hunique k ((g.sample k s).mpr hns) with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Exact pairing gives the Boolean parity equation; triple occupancy is excluded. -/
theorem GridAlignment.parity {C : Config} (g : GridAlignment C)
    (hm : IsMolecule C) (hinj : Function.Injective g.lines)
    (x : Fin 3) (y : Fin 5) (z : Fin 7) :
    bitXor (bitXor (g.present (aLine y z)) (g.present (bLine x z)))
      (g.present (cLine x y)) = false := by
  have hd := site_lines_distinct x y z
  have ha : covers (aLine y z) (site x y z) = true :=
    (site_lines x y z _).mpr (Or.inl rfl)
  have hb : covers (bLine x z) (site x y z) = true :=
    (site_lines x y z _).mpr (Or.inr (Or.inl rfl))
  have hc : covers (cLine x y) (site x y z) = true :=
    (site_lines x y z _).mpr (Or.inr (Or.inr rfl))
  have hpa : g.present (aLine y z) = true →
      g.present (bLine x z) = true ∨ g.present (cLine x y) = true := by
    intro h
    obtain ⟨m, hne, hm', hms, _⟩ := g.present_partner hm hinj _ _ h ha
    have hcases := (site_lines x y z m).mp hms
    aesop
  have hpb : g.present (bLine x z) = true →
      g.present (aLine y z) = true ∨ g.present (cLine x y) = true := by
    intro h
    obtain ⟨m, hne, hm', hms, _⟩ := g.present_partner hm hinj _ _ h hb
    have hcases := (site_lines x y z m).mp hms
    aesop
  have hpc : g.present (cLine x y) = true →
      g.present (aLine y z) = true ∨ g.present (bLine x z) = true := by
    intro h
    obtain ⟨m, hne, hm', hms, _⟩ := g.present_partner hm hinj _ _ h hc
    have hcases := (site_lines x y z m).mp hms
    aesop
  have hnot3 : ¬(g.present (aLine y z) = true ∧
      g.present (bLine x z) = true ∧ g.present (cLine x y) = true) := by
    rintro ⟨h1, h2, h3⟩
    obtain ⟨m, hne, hm', hms, hu⟩ := g.present_partner hm hinj _ _ h1 ha
    have hu2 := hu _ h2 hb
    have hu3 := hu _ h3 hc
    rcases hu2 with hba | hbm
    · exact hd.1 hba.symm
    rcases hu3 with hca | hcm
    · exact hd.2.1 hca.symm
    exact hd.2.2 (hbm.trans hcm.symm)
  cases h1 : g.present (aLine y z) <;>
    cases h2 : g.present (bLine x z) <;>
    cases h3 : g.present (cLine x y) <;>
    simp_all [bitXor]

end CyclicAtoms.Geometry
