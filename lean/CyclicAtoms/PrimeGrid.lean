import CyclicAtoms.UniversalSynthesis
import Mathlib.Tactic

namespace CyclicAtoms.PrimeGrid

abbrev Site (p q r : ℕ) := Fin p × Fin q × Fin r

inductive Line (p q r : ℕ)
  | pLine (y : Fin q) (z : Fin r)
  | qLine (x : Fin p) (z : Fin r)
  | rLine (x : Fin p) (y : Fin q)
  deriving DecidableEq, Fintype

def covers {p q r : ℕ} : Line p q r → Site p q r → Prop
  | .pLine y z, s => s.2.1 = y ∧ s.2.2 = z
  | .qLine x z, s => s.1 = x ∧ s.2.2 = z
  | .rLine x y, s => s.1 = x ∧ s.2.1 = y

instance {p q r : ℕ} (l : Line p q r) (s : Site p q r) : Decidable (covers l s) := by
  cases l <;> unfold covers <;> infer_instance

def element {p q r : ℕ} : Line p q r → ℕ
  | .pLine _ _ => p
  | .qLine _ _ => q
  | .rLine _ _ => r

noncomputable def counts {p q r : ℕ} (S : Finset (Line p q r)) : UniversalSynthesis.Formula := by
  classical
  exact ![(S.filter (fun l => match l with | .pLine _ _ => True | _ => False)).card,
    (S.filter (fun l => match l with | .qLine _ _ => True | _ => False)).card,
    (S.filter (fun l => match l with | .rLine _ _ => True | _ => False)).card]

def Paired {p q r : ℕ} (S : Finset (Line p q r)) : Prop :=
  ∀ s : Site p q r, (S.filter (fun l => covers l s)).card = 0 ∨
    (S.filter (fun l => covers l s)).card = 2

def Adj {p q r : ℕ} (S : Finset (Line p q r)) (l m : Line p q r) : Prop :=
  l ∈ S ∧ m ∈ S ∧ ∃ s, covers l s ∧ covers m s

def Connected {p q r : ℕ} (S : Finset (Line p q r)) : Prop :=
  S.Nonempty ∧ ∀ l ∈ S, ∀ m ∈ S, Relation.ReflTransGen (Adj S) l m

noncomputable def mask {p q r : ℕ} (α : Fin p → Bool) (β : Fin q → Bool) (γ : Fin r → Bool) :
    Finset (Line p q r) := by
  classical
  exact Finset.univ.filter fun l => match l with
    | .pLine y z => β y ≠ γ z
    | .qLine x z => α x ≠ γ z
    | .rLine x y => α x ≠ β y

def weight {n : ℕ} (f : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => f i = true)).card

end CyclicAtoms.PrimeGrid
