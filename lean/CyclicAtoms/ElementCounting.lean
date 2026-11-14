import CyclicAtoms.Defs
import Mathlib.Tactic

namespace CyclicAtoms.Geometry

open scoped BigOperators

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

end CyclicAtoms.Geometry
