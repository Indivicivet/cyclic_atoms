import CyclicAtoms.PrimeGridCounting

namespace CyclicAtoms.PrimeGrid

private def xcoord {p q r : ℕ} (fallback : Fin p) : Line p q r → Fin p
  | .pLine _ _ => fallback
  | .qLine x _ => x
  | .rLine x _ => x

private def qSlice (p q r : ℕ) (x : Fin p) : Fin r ↪ Line p q r where
  toFun z := .qLine x z
  inj' := by intro a b h; simpa using h

private def rSlice (p q r : ℕ) (x : Fin p) : Fin q ↪ Line p q r where
  toFun y := .rLine x y
  inj' := by intro a b h; simpa using h

/-- If p-lines are absent, every bond preserves x. Connectedness then forces
exactly one complete q/r slice, not a disjoint union of binary molecules. -/
theorem binary_of_no_p {p q r : ℕ} (_hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    {S : Finset (Line p q r)} (hpair : Paired S) (hconn : Connected S)
    (hno : ∀ y z, .pLine y z ∉ S) :
    counts S = UniversalSynthesis.binaryQR q r := by
  classical
  have hqr (x : Fin p) (y : Fin q) (z : Fin r) :
      (.qLine x z ∈ S) ↔ (.rLine x y ∈ S) := by
    have h := hpair.parity x y z
    have hn := hno y z
    by_cases hQ : .qLine x z ∈ S <;> by_cases hR : .rLine x y ∈ S <;>
      simp_all [Chemistry.bitXor]
  obtain ⟨l, hl⟩ := hconn.1
  have hex : ∃ x z, .qLine x z ∈ S := by
    cases l with
    | pLine y z => exact False.elim (hno y z hl)
    | qLine x z => exact ⟨x, z, hl⟩
    | rLine x y => exact ⟨x, ⟨0, hr⟩, (hqr x y ⟨0, hr⟩).mpr hl⟩
  obtain ⟨x, z, hxz⟩ := hex
  have hloc (l : Line p q r) (hl : l ∈ S) (s : Site p q r) (hs : covers l s) :
      xcoord x l = s.1 := by
    cases l with
    | pLine y z => exact False.elim (hno y z hl)
    | qLine u v => exact hs.1.symm
    | rLine u v => exact hs.1.symm
  have hstep {l m : Line p q r} (h : Adj S l m) : xcoord x l = xcoord x m := by
    obtain ⟨hl, hm, s, hs, ht⟩ := h
    exact (hloc l hl s hs).trans (hloc m hm s ht).symm
  have hall (l : Line p q r) (hl : l ∈ S) : xcoord x l = x := by
    have hw := hconn.2 (.qLine x z) hxz l hl
    have heq : xcoord (q := q) x (.qLine x z) = xcoord x l := by
      induction hw with
      | refl => rfl
      | tail _ h ih => exact (ih h.1).trans (hstep h)
    exact heq.symm
  have hQ (u : Fin p) (v : Fin r) : .qLine u v ∈ S ↔ u = x := by
    refine ⟨fun h => hall _ h, ?_⟩
    intro hux
    subst u
    exact (hqr x ⟨0, hq⟩ v).mpr ((hqr x ⟨0, hq⟩ z).mp hxz)
  have hR (u : Fin p) (v : Fin q) : .rLine u v ∈ S ↔ u = x := by
    refine ⟨fun h => hall _ h, ?_⟩
    intro hux
    subst u
    exact (hqr x v z).mp hxz
  have hPset : S.filter (fun l => match l with | .pLine _ _ => True | _ => False) = ∅ := by
    ext l
    cases l <;> simp [hno]
  have hQset : S.filter (fun l => match l with | .qLine _ _ => True | _ => False) =
      Finset.univ.map (qSlice p q r x) := by
    ext l
    cases l <;> simp [qSlice, hQ, eq_comm]
  have hRset : S.filter (fun l => match l with | .rLine _ _ => True | _ => False) =
      Finset.univ.map (rSlice p q r x) := by
    ext l
    cases l <;> simp [rSlice, hR, eq_comm]
  ext i
  fin_cases i
  · change (((S.filter (fun l => match l with | .pLine _ _ => True | _ => False)).card : ℕ) : ℤ) = 0
    exact_mod_cast (congrArg Finset.card hPset)
  · change (((S.filter (fun l => match l with | .qLine _ _ => True | _ => False)).card : ℕ) : ℤ) = r
    exact_mod_cast (congrArg Finset.card hQset).trans (by simp)
  · change (((S.filter (fun l => match l with | .rLine _ _ => True | _ => False)).card : ℕ) : ℤ) = q
    exact_mod_cast (congrArg Finset.card hRset).trans (by simp)

def rotateLine (p q r : ℕ) : Line p q r ≃ Line q r p where
  toFun
    | .pLine y z => .rLine y z
    | .qLine x z => .pLine z x
    | .rLine x y => .qLine y x
  invFun
    | .pLine z x => .qLine x z
    | .qLine y x => .rLine x y
    | .rLine y z => .pLine y z
  left_inv := by intro l; cases l <;> rfl
  right_inv := by intro l; cases l <;> rfl

def rotateSet {p q r : ℕ} (S : Finset (Line p q r)) : Finset (Line q r p) :=
  S.map (rotateLine p q r).toEmbedding

theorem rotate_paired {p q r : ℕ} {S : Finset (Line p q r)} (h : Paired S) :
    Paired (rotateSet S) := by
  classical
  intro s
  have heq : S.filter (fun l => covers (rotateLine p q r l) s) =
      S.filter (fun l => covers l (s.2.2, s.1, s.2.1)) := by
    ext l
    cases l <;> simp [rotateLine, covers, and_comm]
  simpa only [rotateSet, Finset.filter_map, Finset.card_map, Function.comp_def,
    Equiv.toEmbedding_apply, heq] using
    h (s.2.2, s.1, s.2.1)

theorem rotate_connected {p q r : ℕ} {S : Finset (Line p q r)} (h : Connected S) :
    Connected (rotateSet S) := by
  classical
  refine ⟨?_, ?_⟩
  · obtain ⟨l, hl⟩ := h.1
    exact ⟨rotateLine p q r l, Finset.mem_map.mpr ⟨l, hl, rfl⟩⟩
  · intro l hl m hm
    obtain ⟨a, ha, hla⟩ := Finset.mem_map.mp hl
    obtain ⟨b, hb, hlb⟩ := Finset.mem_map.mp hm
    rw [← hla, ← hlb]
    apply (h.2 a ha b hb).lift (rotateLine p q r)
    intro u v hadj
    obtain ⟨hu, hv, s, hs, ht⟩ := hadj
    refine ⟨Finset.mem_map.mpr ⟨u, hu, rfl⟩, Finset.mem_map.mpr ⟨v, hv, rfl⟩,
      (s.2.1, s.2.2, s.1), ?_, ?_⟩
    · cases u <;> simpa [rotateLine, covers, and_comm] using hs
    · cases v <;> simpa [rotateLine, covers, and_comm] using ht

theorem rotate_counts {p q r : ℕ} (S : Finset (Line p q r)) :
    counts (rotateSet S) = ![counts S 1, counts S 2, counts S 0] := by
  classical
  ext i
  fin_cases i
  all_goals simp only [counts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.head_cons]
  all_goals change ((_ : Finset (Line q r p)).card : ℤ) = ((_ : Finset (Line p q r)).card : ℤ)
  all_goals congr 1
  all_goals rw [rotateSet, Finset.filter_map, Finset.card_map]
  all_goals congr 1; ext l; cases l <;> simp [rotateLine]

theorem binary_of_no_q {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    {S : Finset (Line p q r)} (hpair : Paired S) (hconn : Connected S)
    (hno : ∀ x z, .qLine x z ∉ S) :
    counts S = UniversalSynthesis.binaryPR p r := by
  classical
  have hno' : ∀ z x, Line.pLine z x ∉ rotateSet S := by
    intro z x hm
    exact hno x z (by simpa [rotateSet, Finset.mem_map_equiv, rotateLine] using hm)
  have h := binary_of_no_p hq hr hp (rotate_paired hpair) (rotate_connected hconn) hno'
  rw [rotate_counts] at h
  ext i
  fin_cases i
  · have hi := congrFun h 2
    simpa [UniversalSynthesis.binaryQR, UniversalSynthesis.binaryPR] using hi
  · have hi := congrFun h 0
    simpa [UniversalSynthesis.binaryQR, UniversalSynthesis.binaryPR] using hi
  · have hi := congrFun h 1
    simpa [UniversalSynthesis.binaryQR, UniversalSynthesis.binaryPR] using hi

theorem binary_of_no_r {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    {S : Finset (Line p q r)} (hpair : Paired S) (hconn : Connected S)
    (hno : ∀ x y, .rLine x y ∉ S) :
    counts S = UniversalSynthesis.binaryPQ p q := by
  classical
  have hno' : ∀ y x, Line.qLine y x ∉ rotateSet S := by
    intro y x hm
    exact hno x y (by simpa [rotateSet, Finset.mem_map_equiv, rotateLine] using hm)
  have h := binary_of_no_q hq hr hp (rotate_paired hpair) (rotate_connected hconn) hno'
  rw [rotate_counts] at h
  ext i
  fin_cases i
  · have hi := congrFun h 2
    simpa [UniversalSynthesis.binaryPR, UniversalSynthesis.binaryPQ] using hi
  · have hi := congrFun h 0
    simpa [UniversalSynthesis.binaryPR, UniversalSynthesis.binaryPQ] using hi
  · have hi := congrFun h 1
    simpa [UniversalSynthesis.binaryPR, UniversalSynthesis.binaryPQ] using hi

/-- The complete formula classification for a paired connected set of
coordinate lines. Repeated original atoms are handled separately as dimers. -/
theorem valid_of_paired_connected {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    {S : Finset (Line p q r)} (hpair : Paired S) (hconn : Connected S) :
    UniversalSynthesis.Valid p q r (counts S) := by
  classical
  by_cases hP : 0 < counts S 0
  · by_cases hQ : 0 < counts S 1
    · by_cases hR : 0 < counts S 2
      · obtain ⟨α, β, γ, rfl⟩ := hpair.mask_exists hp hq hr
        refine Or.inr ⟨weight α, weight β, weight γ, by positivity, ?_, by positivity,
          ?_, by positivity, ?_, ?_, mask_counts α β γ⟩
        · exact_mod_cast weight_le α
        · exact_mod_cast weight_le β
        · exact_mod_cast weight_le γ
        · intro i
          rw [← mask_counts]
          fin_cases i
          · exact hP
          · exact hQ
          · exact hR
      · have hno : ∀ x y, Line.rLine x y ∉ S := by
          intro x y h
          exact hR ((count_r_pos S).mpr ⟨x, y, h⟩)
        rw [binary_of_no_r hp hq hr hpair hconn hno]
        exact Or.inl (by simp)
    · have hno : ∀ x z, Line.qLine x z ∉ S := by
        intro x z h
        exact hQ ((count_q_pos S).mpr ⟨x, z, h⟩)
      rw [binary_of_no_q hp hq hr hpair hconn hno]
      exact Or.inl (by simp)
  · have hno : ∀ y z, Line.pLine y z ∉ S := by
      intro y z h
      exact hP ((count_p_pos S).mpr ⟨y, z, h⟩)
    rw [binary_of_no_p hp hq hr hpair hconn hno]
    exact Or.inl (by simp)

/-- info: 'CyclicAtoms.PrimeGrid.valid_of_paired_connected' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms valid_of_paired_connected

end CyclicAtoms.PrimeGrid
