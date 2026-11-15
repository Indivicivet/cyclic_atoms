import CyclicAtoms.Defs

namespace CyclicAtoms.Chemistry

/-- Finite quantifier decisions for the repository's 2022 Lean toolchain. -/
def decideForallFin : (n : Nat) → (p : Fin n → Prop) →
    [DecidablePred p] → Decidable (∀ i, p i)
  | 0, _, _ => isTrue (fun i => Fin.elim0 i)
  | n + 1, p, _ =>
      if h0 : p ⟨0, Nat.zero_lt_succ n⟩ then
        match decideForallFin n (fun i => p i.succ) with
        | isTrue h => isTrue (fun ⟨i, hi⟩ => match i with
            | 0 => h0
            | k + 1 => h ⟨k, Nat.lt_of_succ_lt_succ hi⟩)
        | isFalse h => isFalse (fun hall => h (fun i => hall i.succ))
      else isFalse (fun hall => h0 (hall ⟨0, Nat.zero_lt_succ n⟩))

instance (n : Nat) (p : Fin n → Prop) [DecidablePred p] :
    Decidable (∀ i, p i) := decideForallFin n p

def decideExistsFin : (n : Nat) → (p : Fin n → Prop) →
    [DecidablePred p] → Decidable (∃ i, p i)
  | 0, _, _ => isFalse (fun ⟨i, _⟩ => Fin.elim0 i)
  | n + 1, p, _ =>
      if h0 : p ⟨0, Nat.zero_lt_succ n⟩ then
        isTrue ⟨⟨0, Nat.zero_lt_succ n⟩, h0⟩
      else match decideExistsFin n (fun i => p i.succ) with
        | isTrue h => isTrue (Exists.elim h (fun i hi => ⟨i.succ, hi⟩))
        | isFalse h => isFalse (fun ⟨⟨i, hi⟩, hp⟩ => match i with
            | 0 => h0 hp
            | k + 1 => h ⟨⟨k, Nat.lt_of_succ_lt_succ hi⟩, hp⟩)

instance (n : Nat) (p : Fin n → Prop) [DecidablePred p] :
    Decidable (∃ i, p i) := decideExistsFin n p

def allFinCheck : (n : Nat) → (Fin n → Bool) → Bool
  | 0, _ => true
  | n + 1, f => f ⟨0, Nat.zero_lt_succ n⟩ && allFinCheck n (fun i => f i.succ)

theorem and_left_true : ∀ a b : Bool, (a && b) = true → a = true := by
  intro a b
  cases a <;> cases b <;> decide

theorem and_right_true : ∀ a b : Bool, (a && b) = true → b = true := by
  intro a b
  cases a <;> cases b <;> decide

/-- A Boolean finite check gives the corresponding universally quantified proof. -/
theorem allFinCheck_sound : ∀ (n : Nat) (f : Fin n → Bool),
    allFinCheck n f = true → ∀ i, f i = true
  | 0, _, _, i => Fin.elim0 i
  | n + 1, f, h, ⟨0, _⟩ => and_left_true _ _ h
  | n + 1, f, h, ⟨k + 1, hk⟩ =>
      allFinCheck_sound n (fun i => f i.succ) (and_right_true _ _ h)
        ⟨k, Nat.lt_of_succ_lt_succ hk⟩

/-- Counts of 3-, 5- and 7-atoms. Reactions do not identify geometric isomers. -/
structure Formula where
  n3 : Nat
  n5 : Nat
  n7 : Nat
  deriving DecidableEq, BEq, Repr

def inventory (molecules : List Formula) : Formula :=
  molecules.foldl (fun total m =>
    ⟨total.n3 + m.n3, total.n5 + m.n5, total.n7 + m.n7⟩) ⟨0, 0, 0⟩

structure Reaction where
  inputs : List Formula
  outputs : List Formula
  deriving Repr

def smallSide (catalog : List Formula) (side : List Formula) : Bool :=
  decide (1 ≤ side.length ∧ side.length ≤ 2) && side.all catalog.contains

/-- The maximally permissive closed-endpoint rule used by the Python search. -/
def validReaction (catalog : List Formula) (r : Reaction) : Bool :=
  smallSide catalog r.inputs && smallSide catalog r.outputs &&
    decide (inventory r.inputs = inventory r.outputs)

def removeOne (m : Formula) : List Formula → Option (List Formula)
  | [] => none
  | a :: rest => if m = a then some rest else
      match removeOne m rest with
      | none => none
      | some remaining => some (a :: remaining)

/-- Repeated inputs are consumed repeatedly: X+X requires two copies of X. -/
def consume : List Formula → List Formula → Option (List Formula)
  | [], stock => some stock
  | m :: rest, stock =>
      match removeOne m stock with
      | none => none
      | some remaining => consume rest remaining

structure Plan where
  initial : List Formula
  steps : List Nat
  deriving Repr

def execute (catalog : List Formula) (reactions : List Reaction) :
    List Nat → List Formula → Option (List Formula)
  | [], stock => some stock
  | i :: rest, stock =>
      match reactions[i]? with
      | none => none
      | some r => if validReaction catalog r then
          match consume r.inputs stock with
          | none => none
          | some remaining => execute catalog reactions rest (r.outputs ++ remaining)
        else none

/-- A fully specified, finite batch. No initial intermediates or loans allowed. -/
def checkPlan (catalog : List Formula) (reactions : List Reaction)
    (feeds : List Formula) (target : Formula) (p : Plan) : Bool :=
  p.initial.all feeds.contains &&
    match execute catalog reactions p.steps p.initial with
    | none => false
    | some stock => stock.contains target

def Synthesizable (catalog : List Formula) (reactions : List Reaction)
    (feeds : List Formula) (target : Formula) : Prop :=
  ∃ p : Plan, checkPlan catalog reactions feeds target p = true

/-- Finite coordinate lines on the 105-site CRT grid. There are 35 3-lines,
21 5-lines, and 15 7-lines. Repeated entries are distinct atom vertices. -/
abbrev Line := Fin 71

def lineElement (a : Line) : Nat :=
  if a.val < 35 then 3 else if a.val < 56 then 5 else 7

def lineOffset (a : Line) : Nat :=
  if a.val < 35 then a.val else if a.val < 56 then a.val - 35 else a.val - 56

def linePeriod (a : Line) : Nat :=
  if a.val < 35 then 35 else if a.val < 56 then 21 else 15

def covers (a : Line) (site : Fin 105) : Bool :=
  site.val % linePeriod a == lineOffset a

def overlaps (a b : Line) : Bool :=
  if lineElement a == lineElement b then lineOffset a == lineOffset b else
    if lineElement a + lineElement b == 8 then lineOffset a % 7 == lineOffset b % 7
    else if lineElement a + lineElement b == 10 then lineOffset a % 5 == lineOffset b % 5
    else lineOffset a % 3 == lineOffset b % 3

def gridFormula (atoms : List Line) : Formula :=
  ⟨(atoms.filter (fun a => lineElement a == 3)).length,
   (atoms.filter (fun a => lineElement a == 5)).length,
   (atoms.filter (fun a => lineElement a == 7)).length⟩

def pairedGrid (atoms : List Line) : Bool :=
  (List.range 105).all (fun x =>
    let n := (atoms.filter (fun a => x % linePeriod a == lineOffset a)).length
    n == 0 || n == 2)

def connectedSearch (atoms : List Line) : Nat → List Nat → Bool
  | 0, reached => reached.length == atoms.length
  | fuel + 1, reached => if reached.length == atoms.length then true else
      connectedSearch atoms fuel ((List.range atoms.length).filter (fun i =>
        reached.contains i || reached.any (fun j =>
          overlaps (atoms.getD i ⟨0, by decide⟩) (atoms.getD j ⟨0, by decide⟩))))

/-- Standard graph search from vertex zero; fuel n permits paths of length n. -/
def moleculeOnGrid (atoms : List Line) : Bool :=
  decide (0 < atoms.length) && pairedGrid atoms && connectedSearch atoms atoms.length [0]

/-- Formula from the weights of the three parity-bit lists. -/
def parityFormula (a : Fin 2) (b : Fin 6) (c : Fin 8) : Formula :=
  ⟨b.val * (7 - c.val) + (5 - b.val) * c.val,
   a.val * (7 - c.val) + (3 - a.val) * c.val,
   a.val * (5 - b.val) + (3 - a.val) * b.val⟩

def threeElements (m : Formula) : Prop := 0 < m.n3 ∧ 0 < m.n5 ∧ 0 < m.n7

instance (m : Formula) : Decidable (threeElements m) := by
  unfold threeElements
  infer_instance

/-- The Boolean equation behind paired coordinate-line configurations. -/
def bitXor (a b : Bool) : Bool := a != b

private theorem parity_first : ∀ a b c : Bool,
    bitXor (bitXor a b) c = false → a = bitXor c b := by
  intro a b c
  cases a <;> cases b <;> cases c <;> decide

private theorem parity_second : ∀ a b c d e : Bool,
    bitXor (bitXor a b) c = false →
    bitXor (bitXor a d) e = false →
    c = bitXor (bitXor b d) e := by
  intro a b c d e
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

private theorem parity_third : ∀ a b c d e f : Bool,
    bitXor (bitXor a b) c = false →
    bitXor (bitXor a d) e = false →
    c = bitXor f e → b = bitXor f d := by
  intro a b c d e f
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

/-- Every paired Boolean line system has the three-list parity form.
The index types can be arbitrary; no finite enumeration is used here. -/
theorem parity_factorization {X Y Z : Type} (x0 : X) (y0 : Y) (z0 : Z)
    (A : Y → Z → Bool) (B : X → Z → Bool) (C : X → Y → Bool)
    (h : ∀ x y z, bitXor (bitXor (A y z) (B x z)) (C x y) = false) :
    ∃ (α : X → Bool) (β : Y → Bool) (γ : Z → Bool),
      (∀ y z, A y z = bitXor (β y) (γ z)) ∧
      (∀ x z, B x z = bitXor (α x) (γ z)) ∧
      (∀ x y, C x y = bitXor (α x) (β y)) := by
  refine ⟨(fun x => bitXor (B x z0) (B x0 z0)), C x0, B x0, ?_⟩
  constructor
  · intro y z
    exact parity_first _ _ _ (h x0 y z)
  constructor
  · intro x z
    have hc := parity_second _ _ _ _ _ (h x y0 z0) (h x0 y0 z0)
    exact parity_third _ _ _ _ _ _ (h x y0 z) (h x0 y0 z) hc
  · intro x y
    exact parity_second _ _ _ _ _ (h x y z0) (h x0 y z0)

end CyclicAtoms.Chemistry
