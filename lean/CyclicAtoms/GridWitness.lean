import CyclicAtoms.Counting357

namespace CyclicAtoms.Geometry

open Chemistry

theorem circle_zero : circle Phase.zero = 0 := by simp [circle, Phase.zero]

def lineAtom (l : Line) : Atom :=
  ⟨lineElement l, Phase.ofRat (lineOffset l) 105 (by decide),
    (by native_decide : ∀ l : Line, 2 ≤ lineElement l) l⟩

def realizeLines (atoms : List Line) : Config := atoms.map lineAtom

theorem lineAtom_points (l : Line) (x : Phase) :
    (lineAtom l).hasPoint x ↔ ∃ s : ZMod 105,
      covers l s = true ∧ circle x = grid s := by
  have hp := (by native_decide : ∀ l : Line,
    lineElement l = 3 ∨ lineElement l = 5 ∨ lineElement l = 7) l
  have hk : circle (lineAtom l).phase =
      circle Phase.zero + grid ((lineOffset l : Nat) : ZMod 105) := by
    rw [circle_zero, zero_add, ZMod.toAddCircle_natCast]
    rfl
  have hline := (by native_decide : ∀ l : Line,
    lineFor (lineElement l) ((lineOffset l : Nat) : ZMod 105) = l) l
  have h := aligned_atom_hasPoint (lineAtom l) hp Phase.zero _ hk x
  simpa only [lineAtom, hline, circle_zero, zero_add] using h

def sourceIndex (atoms : List Line) (i : Fin (realizeLines atoms).length) : Fin atoms.length :=
  ⟨i.val, by simpa only [realizeLines, List.length_map] using i.isLt⟩

theorem realizeLines_get (atoms : List Line) (i : Fin (realizeLines atoms).length) :
    (realizeLines atoms).get i = lineAtom (atoms.get (sourceIndex atoms i)) := by
  simp [realizeLines, sourceIndex, List.get_eq_getElem]

def canonicalAlignment (atoms : List Line) : GridAlignment (realizeLines atoms) where
  origin := Phase.zero
  lines := fun i => atoms.get (sourceIndex atoms i)
  element := fun i => by rw [realizeLines_get]; rfl
  points := fun i x => by
    rw [realizeLines_get, lineAtom_points]
    simp only [circle_zero, zero_add]

theorem realizeLines_multiplicity (atoms : List Line) (p : Nat) :
    (realizeLines atoms).multiplicity p =
      (atoms.filter (fun l => lineElement l == p)).length := by
  induction atoms with
  | nil => rfl
  | cons a atoms ih =>
    cases h : lineElement a == p <;>
      simp_all [realizeLines, Config.multiplicity, lineAtom]

theorem realizeLines_formula (atoms : List Line) :
    configFormula (realizeLines atoms) = gridFormula atoms := by
  unfold configFormula gridFormula
  rw [realizeLines_multiplicity, realizeLines_multiplicity, realizeLines_multiplicity]

theorem realizeLines_elements (atoms : List Line) : Elements357 (realizeLines atoms) := by
  intro i
  rw [realizeLines_get]
  exact (by native_decide : ∀ l : Line,
    lineElement l = 3 ∨ lineElement l = 5 ∨ lineElement l = 7) _

theorem overlaps_iff_site : ∀ a b : Line,
    overlaps a b = true ↔ ∃ s : ZMod 105, covers a s = true ∧ covers b s = true := by
  native_decide

theorem GridAlignment.at_site {C : Config} (g : GridAlignment C) (x : Phase)
    (s : ZMod 105) (hx : circle x = circle g.origin + grid s) (i : Fin C.length) :
    (C.get i).hasPoint x ↔ covers (g.lines i) s = true := by
  rw [g.points]
  constructor
  · rintro ⟨t, ht, heq⟩
    rw [hx, add_left_cancel_iff] at heq
    have hst := ZMod.toAddCircle_injective 105 heq
    simpa [hst] using ht
  · intro hs
    exact ⟨s, hs, hx⟩

theorem GridAlignment.bond {C : Config} (g : GridAlignment C) {i j : Fin C.length}
    (hne : i ≠ j) (h : overlaps (g.lines i) (g.lines j) = true) : BondAdj C i j := by
  obtain ⟨s, hi, hj⟩ := (overlaps_iff_site _ _).mp h
  exact ⟨gridPoint g.origin s, hne, (g.sample i s).mpr hi, (g.sample j s).mpr hj⟩

structure TreeCertificate where
  ranks : List Nat
  parents : List Nat

def TreeCertificate.rank {n : Nat} (t : TreeCertificate) (i : Fin n) : Nat :=
  t.ranks.getD i.val 0

def TreeCertificate.parent {n : Nat} (t : TreeCertificate) (i : Fin n) : Fin n :=
  ⟨t.parents.getD i.val 0 % n,
    Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩

def FinitePairing {C : Config} (g : GridAlignment C) : Prop :=
  ∀ s : ZMod 105,
    (Finset.univ.filter (fun i => covers (g.lines i) s = true)).card = 0 ∨
    (Finset.univ.filter (fun i => covers (g.lines i) s = true)).card = 2

def TreeCondition {C : Config} (g : GridAlignment C) (t : TreeCertificate) : Prop :=
  0 < C.length ∧ ∀ i : Fin C.length, i.val = 0 ∨
    (t.rank (t.parent i) < t.rank i ∧ overlaps (g.lines (t.parent i)) (g.lines i) = true)

instance {C : Config} (g : GridAlignment C) : Decidable (FinitePairing g) := by
  unfold FinitePairing
  infer_instance

instance {C : Config} (g : GridAlignment C) (t : TreeCertificate) :
    Decidable (TreeCondition g t) := by
  unfold TreeCondition
  infer_instance

theorem reachable_trans {C : Config} {i j k : Fin C.length}
    (hij : BondReachable C i j) (hjk : BondReachable C j k) : BondReachable C i k := by
  induction hij with
  | refl => exact hjk
  | step h _ ih => exact .step h (ih hjk)

theorem reachable_symm {C : Config} {i j : Fin C.length}
    (hij : BondReachable C i j) : BondReachable C j i := by
  induction hij with
  | refl => exact .refl _
  | step h _ ih => exact reachable_trans ih (.step (bondAdj_symm C h) (.refl _))

/-- Rank decreases along certified parent edges, so every vertex reaches the root. -/
theorem GridAlignment.connected_of_tree {C : Config} (g : GridAlignment C)
    (t : TreeCertificate) (ht : TreeCondition g t) : IsConnected C := by
  let root : Fin C.length := ⟨0, ht.1⟩
  have hr : ∀ r : Nat, ∀ i : Fin C.length, t.rank i = r → BondReachable C root i := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro i hri
      rcases ht.2 i with hi | ⟨hlt, he⟩
      · have hi' : i = root := Fin.ext hi
        subst i
        exact .refl _
      · have hne : t.parent i ≠ i := by
          intro heq
          rw [heq] at hlt
          exact Nat.lt_irrefl _ hlt
        have hp := ih (t.rank (t.parent i)) (by simpa [hri] using hlt) (t.parent i) rfl
        exact reachable_trans hp (.step (g.bond hne he) (.refl _))
  exact ⟨ht.1, fun i j => reachable_trans (reachable_symm (hr _ i rfl)) (hr _ j rfl)⟩

/-- Finite occupancy and a tree certificate imply the original infinite-point predicate. -/
theorem GridAlignment.isMolecule {C : Config} (g : GridAlignment C)
    (hpair : FinitePairing g) (t : TreeCertificate) (ht : TreeCondition g t) : IsMolecule C := by
  refine ⟨g.connected_of_tree t ht, ?_⟩
  intro i x hi
  obtain ⟨s, hs, hx⟩ := (g.points i x).mp hi
  let W := Finset.univ.filter (fun k => covers (g.lines k) s = true)
  have hiW : i ∈ W := by simp [W, hs]
  have htwo : W.card = 2 := (hpair s).resolve_left
    (Finset.card_ne_zero.mpr ⟨i, hiW⟩)
  obtain ⟨a, b, hab, hW⟩ := Finset.card_eq_two.mp htwo
  have hiab : i = a ∨ i = b := by simpa [hW] using hiW
  have hp : ∀ k : Fin C.length, k ∈ W ↔ (C.get k).hasPoint x := by
    intro k
    simpa [W] using (g.at_site x s hx k).symm
  have hu : ∀ k : Fin C.length, (C.get k).hasPoint x → k = a ∨ k = b := by
    intro k hk
    simpa [hW] using (hp k).mpr hk
  have ha : (C.get a).hasPoint x := (hp a).mp (by simp [hW])
  have hb : (C.get b).hasPoint x := (hp b).mp (by simp [hW])
  rcases hiab with rfl | rfl
  · exact ⟨b, hab, hb, hu⟩
  · exact ⟨a, hab.symm, ha, fun k hk => (hu k hk).symm⟩

end CyclicAtoms.Geometry
