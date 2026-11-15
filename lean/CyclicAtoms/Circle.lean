import CyclicAtoms.Defs
import Mathlib.Topology.Instances.AddCircle
import Mathlib.Tactic

namespace CyclicAtoms.Geometry

noncomputable def circle (a : Phase) : UnitAddCircle :=
  ((a.num : ℝ) / a.den : ℝ)

/-- The original cross-multiplication/modulo definition is equality on ℝ/ℤ. -/
theorem phase_equiv_iff_circle (a b : Phase) :
    Phase.Equiv a b ↔ circle a = circle b := by
  have ha : (a.den : ℝ) ≠ 0 := by exact_mod_cast a.den_pos.ne'
  have hb : (b.den : ℝ) ≠ 0 := by exact_mod_cast b.den_pos.ne'
  have hden : ((a.den * b.den : ℕ) : ℝ) ≠ 0 := by
    push_cast
    exact mul_ne_zero ha hb
  have hfa : (a.num : ℝ) / a.den =
      ((a.num * b.den : ℕ) : ℝ) / ((a.den * b.den : ℕ) : ℝ) := by
    push_cast
    field_simp
    ring
  have hfb : (b.num : ℝ) / b.den =
      ((b.num * a.den : ℕ) : ℝ) / ((a.den * b.den : ℕ) : ℝ) := by
    push_cast
    field_simp
    ring
  change Nat.ModEq (a.den * b.den) (a.num * b.den) (b.num * a.den) ↔ _
  rw [← AddCommGroup.natCast_modEq_natCast (α := ℝ)]
  change _ ↔ (((a.num : ℝ) / a.den : ℝ) : UnitAddCircle) =
    (((b.num : ℝ) / b.den : ℝ) : UnitAddCircle)
  rw [hfa, hfb, eq_comm, ← AddCommGroup.modEq_iff_eq_mod_zmultiples,
    AddCommGroup.div_modEq_div hden, one_mul]

theorem circle_add (a b : Phase) :
    circle (Phase.add a b) = circle a + circle b := by
  change (((a.num * b.den + b.num * a.den : ℕ) : ℝ) /
    ((a.den * b.den : ℕ) : ℝ) : UnitAddCircle) =
      (((a.num : ℝ) / a.den : ℝ) : UnitAddCircle) +
      (((b.num : ℝ) / b.den : ℝ) : UnitAddCircle)
  rw [← AddCircle.coe_add]
  congr 1
  push_cast
  have ha : (a.den : ℝ) ≠ 0 := by exact_mod_cast a.den_pos.ne'
  have hb : (b.den : ℝ) ≠ 0 := by exact_mod_cast b.den_pos.ne'
  field_simp

noncomputable abbrev grid : ZMod 105 →+ UnitAddCircle := ZMod.toAddCircle

def gridPoint (θ : Phase) (s : ZMod 105) : Phase :=
  Phase.add θ (Phase.ofRat s.val 105 (by decide))

theorem circle_gridPoint (θ : Phase) (s : ZMod 105) :
    circle (gridPoint θ s) = circle θ + grid s := by
  rw [gridPoint, circle_add]
  congr 1

def Elements357 (C : Config) : Prop :=
  ∀ i : Fin C.length, (C.get i).p = 3 ∨ (C.get i).p = 5 ∨ (C.get i).p = 7

theorem circle_point (A : Atom) (hp : A.p = 3 ∨ A.p = 5 ∨ A.p = 7)
    (k : Fin A.p) :
    circle (A.point k) = circle A.phase + grid ((105 / A.p * k.val : ℕ) : ZMod 105) := by
  rw [Atom.point, circle_add]
  congr 1
  rw [ZMod.toAddCircle_natCast]
  change (((k.val : ℝ) / A.p : ℝ) : UnitAddCircle) = _
  congr 1
  generalize k.val = n
  rcases hp with hp | hp | hp <;> rw [hp] <;> push_cast <;> ring

theorem hasPoint_iff_circle (A : Atom) (x : Phase) :
    A.hasPoint x ↔ ∃ k : Fin A.p, circle x = circle (A.point k) := by
  simp only [Atom.hasPoint, phase_equiv_iff_circle]

/-- Crossing a bond changes phase by a multiple of 1/105. -/
theorem bond_grid_difference {C : Config} (hC : Elements357 C)
    {i j : Fin C.length} (h : BondAdj C i j) :
    ∃ s : ZMod 105, circle (C.get j).phase = circle (C.get i).phase + grid s := by
  obtain ⟨x, _, hi, hj⟩ := h
  obtain ⟨ki, hki⟩ := (hasPoint_iff_circle _ _).mp hi
  obtain ⟨kj, hkj⟩ := (hasPoint_iff_circle _ _).mp hj
  rw [circle_point _ (hC i)] at hki
  rw [circle_point _ (hC j)] at hkj
  refine ⟨(105 / (C.get i).p * ki.val : ℕ) -
    (105 / (C.get j).p * kj.val : ℕ), ?_⟩
  rw [map_sub]
  have hh := hki.symm.trans hkj
  exact (eq_sub_iff_add_eq.mpr hh.symm).trans (by abel)

theorem reachable_grid_difference {C : Config} (hC : Elements357 C)
    {i j : Fin C.length} (h : BondReachable C i j) :
    ∃ s : ZMod 105, circle (C.get j).phase = circle (C.get i).phase + grid s := by
  induction h with
  | refl i => exact ⟨0, by simp⟩
  | @step i j k hij _ ih =>
    obtain ⟨s, hs⟩ := bond_grid_difference hC hij
    obtain ⟨t, ht⟩ := ih
    exact ⟨s + t, by rw [ht, hs, map_add, add_assoc]⟩

/-- Alignment is derived from the original connectedness predicate. -/
theorem connected_grid_alignment {C : Config} (hC : Elements357 C)
    (hc : IsConnected C) :
    ∃ θ : Phase, ∀ i : Fin C.length, ∃ s : ZMod 105,
      circle (C.get i).phase = circle θ + grid s := by
  let root : Fin C.length := ⟨0, hc.1⟩
  exact ⟨(C.get root).phase, fun i => reachable_grid_difference hC (hc.2 root i)⟩

end CyclicAtoms.Geometry
