import CyclicAtoms.Circle
import CyclicAtoms.Chemistry

namespace CyclicAtoms.Geometry

open Chemistry

def lineFor (p : Nat) (s : ZMod 105) : Line :=
  if p = 3 then ⟨s.val % 35, by have := Nat.mod_lt s.val (by decide : 0 < 35); omega⟩
  else if p = 5 then
    ⟨35 + s.val % 21, by have := Nat.mod_lt s.val (by decide : 0 < 21); omega⟩
  else ⟨56 + s.val % 15, by have := Nat.mod_lt s.val (by decide : 0 < 15); omega⟩

theorem lineFor_element (p : Nat) (hp : p = 3 ∨ p = 5 ∨ p = 7) (s : ZMod 105) :
    lineElement (lineFor p s) = p := by
  rcases hp with rfl | rfl | rfl <;> revert s <;> native_decide

/-- This finite identity is the coordinate-line/orbit identification. -/
theorem lineFor_orbit (p : Nat) (hp : p = 3 ∨ p = 5 ∨ p = 7)
    (k s : ZMod 105) :
    covers (lineFor p k) s = true ↔
      ∃ j : Fin p, s = k + ((105 / p * j.val : Nat) : ZMod 105) := by
  rcases hp with rfl | rfl | rfl <;> revert k s <;> native_decide

def site (x : Fin 3) (y : Fin 5) (z : Fin 7) : ZMod 105 :=
  ((70 * x.val + 21 * y.val + 15 * z.val : Nat) : ZMod 105)

def aLine (y : Fin 5) (z : Fin 7) : Line := lineFor 3 (site 0 y z)
def bLine (x : Fin 3) (z : Fin 7) : Line := lineFor 5 (site x 0 z)
def cLine (x : Fin 3) (y : Fin 5) : Line := lineFor 7 (site x y 0)

theorem site_surjective : ∀ s : ZMod 105,
    ∃ x : Fin 3, ∃ y : Fin 5, ∃ z : Fin 7, site x y z = s := by native_decide

theorem site_lines : ∀ (x : Fin 3) (y : Fin 5) (z : Fin 7) (l : Line),
    covers l (site x y z) = true ↔
      l = aLine y z ∨ l = bLine x z ∨ l = cLine x y := by native_decide

theorem site_lines_distinct : ∀ (x : Fin 3) (y : Fin 5) (z : Fin 7),
    aLine y z ≠ bLine x z ∧ aLine y z ≠ cLine x y ∧
      bLine x z ≠ cLine x y := by native_decide

/-- A grid-aligned atom has precisely the sites of one coordinate line. -/
theorem aligned_atom_hasPoint (A : Atom) (hp : A.p = 3 ∨ A.p = 5 ∨ A.p = 7)
    (θ : Phase) (k : ZMod 105) (hk : circle A.phase = circle θ + grid k)
    (x : Phase) :
    A.hasPoint x ↔ ∃ s : ZMod 105,
      covers (lineFor A.p k) s = true ∧ circle x = circle θ + grid s := by
  rw [hasPoint_iff_circle]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨k + ((105 / A.p * j.val : Nat) : ZMod 105),
      (lineFor_orbit A.p hp _ _).mpr ⟨j, rfl⟩, ?_⟩
    rw [hj, circle_point A hp, hk, map_add, add_assoc]
  · rintro ⟨s, hs, hx⟩
    obtain ⟨j, rfl⟩ := (lineFor_orbit A.p hp _ _).mp hs
    refine ⟨j, ?_⟩
    rw [hx, circle_point A hp, hk, map_add, add_assoc]

/-- Membership at a sampled site agrees with the finite line predicate. -/
theorem aligned_atom_sample (A : Atom) (hp : A.p = 3 ∨ A.p = 5 ∨ A.p = 7)
    (θ : Phase) (k : ZMod 105) (hk : circle A.phase = circle θ + grid k)
    (s : ZMod 105) :
    A.hasPoint (gridPoint θ s) ↔ covers (lineFor A.p k) s = true := by
  rw [aligned_atom_hasPoint A hp θ k hk]
  constructor
  · rintro ⟨t, ht, heq⟩
    rw [circle_gridPoint, add_left_cancel_iff] at heq
    have hst := ZMod.toAddCircle_injective 105 heq
    simpa [hst] using ht
  · intro hs
    exact ⟨s, hs, circle_gridPoint θ s⟩

end CyclicAtoms.Geometry
