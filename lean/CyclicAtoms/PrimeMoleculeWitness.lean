import CyclicAtoms.PrimeGeometry
import CyclicAtoms.PrimeGridRealization

namespace CyclicAtoms.PrimeGeometry

open PrimeGrid Geometry

namespace Parameters

noncomputable def realize (t : Parameters) (S : Finset (Line t.p t.q t.r)) : Config :=
  S.toList.map t.lineAtom

noncomputable def sourceIndex (t : Parameters) (S : Finset (Line t.p t.q t.r))
    (i : Fin (t.realize S).length) : Fin S.toList.length :=
  ⟨i.val, by simpa only [realize, List.length_map] using i.isLt⟩

noncomputable def lineAt (t : Parameters) (S : Finset (Line t.p t.q t.r))
    (i : Fin (t.realize S).length) : Line t.p t.q t.r :=
  S.toList.get (t.sourceIndex S i)

theorem realize_get (t : Parameters) (S : Finset (Line t.p t.q t.r))
    (i : Fin (t.realize S).length) :
    (t.realize S).get i = t.lineAtom (t.lineAt S i) := by
  simp [realize, lineAt, sourceIndex, List.get_eq_getElem]

theorem lineAt_mem (t : Parameters) (S : Finset (Line t.p t.q t.r))
    (i : Fin (t.realize S).length) : t.lineAt S i ∈ S := by
  exact Finset.mem_toList.mp (List.get_mem S.toList (t.sourceIndex S i))

theorem lineAt_injective (t : Parameters) (S : Finset (Line t.p t.q t.r)) :
    Function.Injective (t.lineAt S) := by
  intro i j h
  have hi : t.sourceIndex S i = t.sourceIndex S j :=
    S.nodup_toList.get_inj_iff.mp h
  exact Fin.ext (congrArg (fun k : Fin S.toList.length => k.val) hi)

theorem lineAt_surjective (t : Parameters) (S : Finset (Line t.p t.q t.r))
    (l : Line t.p t.q t.r) (hl : l ∈ S) :
    ∃ i : Fin (t.realize S).length, t.lineAt S i = l := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp (Finset.mem_toList.mpr hl)
  refine ⟨⟨i.val, by simpa [realize] using i.isLt⟩, ?_⟩
  simpa only [lineAt, sourceIndex] using hi

theorem realize_elements (t : Parameters) (S : Finset (Line t.p t.q t.r)) :
    t.Elements (t.realize S) := by
  intro i
  rw [t.realize_get]
  cases t.lineAt S i <;> simp [lineAtom, element]

theorem realize_at_site (t : Parameters) (S : Finset (Line t.p t.q t.r))
    (i : Fin (t.realize S).length) (x : Phase) (s : ZMod t.N)
    (hx : circle x = t.grid s) :
    ((t.realize S).get i).hasPoint x ↔ covers (t.lineAt S i) (t.coordinates s) := by
  rw [t.realize_get, t.lineAtom_points]
  constructor
  · rintro ⟨u, hu, hxu⟩
    have heq : s = u := ZMod.toAddCircle_injective t.N (hx.symm.trans hxu)
    simpa only [heq] using hu
  · intro hi
    exact ⟨s, hi, hx⟩

private theorem bondReachable_trans {C : Config} {i j k : Fin C.length}
    (h : BondReachable C i j) (h' : BondReachable C j k) : BondReachable C i k := by
  induction h with
  | refl => exact h'
  | step hs _ ih => exact .step hs (ih h')

theorem realize_bond (t : Parameters) (S : Finset (Line t.p t.q t.r))
    {i j : Fin (t.realize S).length} (hne : i ≠ j)
    (h : Adj S (t.lineAt S i) (t.lineAt S j)) : BondAdj (t.realize S) i j := by
  obtain ⟨_, _, u, hi, hj⟩ := h
  let s := t.coordinates.symm u
  have hx : circle (t.sample Phase.zero s) = t.grid s := by
    simpa [circle, Phase.zero] using t.circle_sample Phase.zero s
  refine ⟨t.sample Phase.zero s, hne, ?_, ?_⟩
  · exact (t.realize_at_site S i _ s hx).mpr (by simpa [s] using hi)
  · exact (t.realize_at_site S j _ s hx).mpr (by simpa [s] using hj)

theorem realize_connected (t : Parameters) (S : Finset (Line t.p t.q t.r))
    (hS : Connected S) : IsConnected (t.realize S) := by
  classical
  have hn : 0 < (t.realize S).length := by
    simpa [realize] using hS.1.card_pos
  refine ⟨hn, ?_⟩
  have hlift : ∀ {l m : Line t.p t.q t.r}, Relation.ReflTransGen (Adj S) l m →
      ∀ (i : Fin (t.realize S).length), t.lineAt S i = l →
      ∀ (j : Fin (t.realize S).length), t.lineAt S j = m →
      BondReachable (t.realize S) i j := by
    intro l m hp
    induction hp with
    | refl =>
      intro i hi j hj
      have heq := t.lineAt_injective S (hi.trans hj.symm)
      subst j
      exact .refl _
    | @tail m n hp hadj ih =>
      intro i hi j hj
      obtain ⟨k, hk⟩ := t.lineAt_surjective S m hadj.1
      have hr := ih i hi k hk
      by_cases hkj : k = j
      · simpa [hkj] using hr
      · apply bondReachable_trans hr
        exact .step (t.realize_bond S hkj (by simpa [hk, hj] using hadj)) (.refl _)
  intro i j
  exact hlift (hS.2 _ (t.lineAt_mem S i) _ (t.lineAt_mem S j)) i rfl j rfl

theorem realize_isMolecule (t : Parameters) (S : Finset (Line t.p t.q t.r))
    (hpair : Paired S) (hconn : Connected S) : IsMolecule (t.realize S) := by
  classical
  refine ⟨t.realize_connected S hconn, ?_⟩
  intro i x hi
  obtain ⟨s, hs, hx⟩ := (t.lineAtom_points (t.lineAt S i) x).mp
    (by simpa only [t.realize_get] using hi)
  let W := S.filter (fun l => covers l (t.coordinates s))
  have hiW : t.lineAt S i ∈ W := Finset.mem_filter.mpr ⟨t.lineAt_mem S i, hs⟩
  have htwo : W.card = 2 := (hpair _).resolve_left
    (Finset.card_ne_zero.mpr ⟨_, hiW⟩)
  obtain ⟨a, b, hab, hW⟩ := Finset.card_eq_two.mp htwo
  have hiab : t.lineAt S i = a ∨ t.lineAt S i = b := by simpa [hW] using hiW
  have hmem : ∀ k : Fin (t.realize S).length,
      t.lineAt S k ∈ W ↔ ((t.realize S).get k).hasPoint x := by
    intro k
    simpa only [W, Finset.mem_filter, t.lineAt_mem S k, true_and] using
      (t.realize_at_site S k x s hx).symm
  have haS : a ∈ S := (Finset.mem_filter.mp (show a ∈ W from by simp [hW])).1
  have hbS : b ∈ S := (Finset.mem_filter.mp (show b ∈ W from by simp [hW])).1
  obtain ⟨ia, hia⟩ := t.lineAt_surjective S a haS
  obtain ⟨ib, hib⟩ := t.lineAt_surjective S b hbS
  have hu : ∀ k : Fin (t.realize S).length, ((t.realize S).get k).hasPoint x →
      k = ia ∨ k = ib := by
    intro k hk
    have hk' := (hmem k).mpr hk
    rw [hW, Finset.mem_insert, Finset.mem_singleton] at hk'
    exact hk'.imp (fun h => t.lineAt_injective S (h.trans hia.symm))
      (fun h => t.lineAt_injective S (h.trans hib.symm))
  have ha : ((t.realize S).get ia).hasPoint x := (hmem ia).mp (by simp [hia, hW])
  have hb : ((t.realize S).get ib).hasPoint x := (hmem ib).mp (by simp [hib, hW])
  have hne : ia ≠ ib := by intro h; exact hab (hia.symm.trans ((congrArg (t.lineAt S) h).trans hib))
  rcases hiab with hiab | hiab
  · have hii : i = ia := t.lineAt_injective S (hiab.trans hia.symm)
    subst i
    exact ⟨ib, hne, hb, hu⟩
  · have hii : i = ib := t.lineAt_injective S (hiab.trans hib.symm)
    subst i
    exact ⟨ia, hne.symm, ha, fun k hk => (hu k hk).symm⟩

theorem realize_multiplicity (t : Parameters) (S : Finset (Line t.p t.q t.r)) (e : ℕ) :
    (t.realize S).multiplicity e = (S.filter (fun l => element l = e)).card := by
  classical
  have hlist : ∀ atoms : List (Line t.p t.q t.r),
      ((atoms.map t.lineAtom).filter (fun A => A.p == e)).length =
        (atoms.filter (fun l => element l == e)).length := by
    intro atoms
    induction atoms with
    | nil => rfl
    | cons a atoms ih =>
      cases ha : element a == e <;>
        simp_all [lineAtom]
  rw [Config.multiplicity, realize, hlist]
  have hset : (S.toList.filter (fun l => element l == e)).toFinset =
      S.filter (fun l => element l = e) := by
    ext l
    simp
  rw [← hset, List.toFinset_card_of_nodup (S.nodup_toList.filter _)]

theorem realize_formula (t : Parameters) (S : Finset (Line t.p t.q t.r)) :
    ![((t.realize S).multiplicity t.p : ℤ), (t.realize S).multiplicity t.q,
      (t.realize S).multiplicity t.r] = counts S := by
  classical
  have hp : S.filter (fun l => element l = t.p) =
      S.filter (fun l => match l with | .pLine _ _ => True | _ => False) := by
    ext l; cases l <;> simp [element, t.pq, t.pr, t.pq.symm, t.pr.symm]
  have hq : S.filter (fun l => element l = t.q) =
      S.filter (fun l => match l with | .qLine _ _ => True | _ => False) := by
    ext l; cases l <;> simp [element, t.pq, t.qr, t.pq.symm, t.qr.symm]
  have hr : S.filter (fun l => element l = t.r) =
      S.filter (fun l => match l with | .rLine _ _ => True | _ => False) := by
    ext l; cases l <;> simp [element, t.pr, t.qr, t.pr.symm, t.qr.symm]
  rw [t.realize_multiplicity S t.p, t.realize_multiplicity S t.q,
    t.realize_multiplicity S t.r, hp, hq, hr]
  ext i
  fin_cases i <;> simp only [counts, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons]
  all_goals apply congrArg (fun T : Finset (Line t.p t.q t.r) => (T.card : ℤ))
  all_goals ext l; cases l <;> simp

theorem identical_pair_isMolecule (A : Atom) : IsMolecule [A, A] := by
  have hpoint : A.hasPoint (A.point ⟨0, A.p_pos⟩) :=
    ⟨⟨0, A.p_pos⟩, Phase.equiv_refl _⟩
  have hb : BondAdj [A, A] ⟨0, by simp⟩ ⟨1, by simp⟩ :=
    ⟨A.point ⟨0, A.p_pos⟩, by simp, hpoint, hpoint⟩
  refine ⟨⟨by simp, ?_⟩, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j
    · exact .refl _
    · exact .step hb (.refl _)
    · exact .step (bondAdj_symm _ hb) (.refl _)
    · exact .refl _
  · intro i x hx
    fin_cases i
    · refine ⟨⟨1, by simp⟩, by simp, hx, ?_⟩
      intro k hk
      fin_cases k <;> simp
    · refine ⟨⟨0, by simp⟩, by simp, hx, ?_⟩
      intro k hk
      fin_cases k <;> simp

theorem every_valid_realizable (t : Parameters) {f : UniversalSynthesis.Formula}
    (hf : UniversalSynthesis.Valid t.p t.q t.r f) :
    ∃ C : Config, IsMolecule C ∧ t.Elements C ∧
      ![(C.multiplicity t.p : ℤ), C.multiplicity t.q, C.multiplicity t.r] = f := by
  rcases valid_grid_witness t.primeP.two_le t.primeQ.two_le t.primeR.two_le hf with
    hd | ⟨S, hpair, hconn, hcounts⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · let A : Atom := ⟨t.p, Phase.zero, t.primeP.two_le⟩
      refine ⟨[A, A], identical_pair_isMolecule A, ?_, ?_⟩
      · intro i; fin_cases i <;> simp [A]
      · ext i; fin_cases i <;>
          simp [A, Config.multiplicity, UniversalSynthesis.dimerP, t.pq, t.pr]
    · let A : Atom := ⟨t.q, Phase.zero, t.primeQ.two_le⟩
      refine ⟨[A, A], identical_pair_isMolecule A, ?_, ?_⟩
      · intro i; fin_cases i <;> simp [A]
      · ext i; fin_cases i <;>
          simp [A, Config.multiplicity, UniversalSynthesis.dimerQ, t.pq.symm, t.qr]
    · let A : Atom := ⟨t.r, Phase.zero, t.primeR.two_le⟩
      refine ⟨[A, A], identical_pair_isMolecule A, ?_, ?_⟩
      · intro i; fin_cases i <;> simp [A]
      · ext i; fin_cases i <;>
          simp [A, Config.multiplicity, UniversalSynthesis.dimerR, t.pr.symm, t.qr.symm]
  · exact ⟨t.realize S, t.realize_isMolecule S hpair hconn, t.realize_elements S,
      (t.realize_formula S).trans hcounts⟩

end Parameters
end CyclicAtoms.PrimeGeometry
