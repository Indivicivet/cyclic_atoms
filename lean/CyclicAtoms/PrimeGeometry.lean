import CyclicAtoms.Circle
import CyclicAtoms.Elementary
import CyclicAtoms.PrimeGrid

namespace CyclicAtoms.PrimeGeometry

open Geometry PrimeGrid

structure Parameters where
  p : ℕ
  q : ℕ
  r : ℕ
  primeP : Nat.Prime p
  primeQ : Nat.Prime q
  primeR : Nat.Prime r
  pq : p ≠ q
  pr : p ≠ r
  qr : q ≠ r

namespace Parameters

instance (t : Parameters) : NeZero t.p := ⟨t.primeP.ne_zero⟩
instance (t : Parameters) : NeZero t.q := ⟨t.primeQ.ne_zero⟩
instance (t : Parameters) : NeZero t.r := ⟨t.primeR.ne_zero⟩

def N (t : Parameters) : ℕ := t.p * (t.q * t.r)

instance (t : Parameters) : NeZero t.N :=
  ⟨Nat.ne_of_gt (Nat.mul_pos t.primeP.pos (Nat.mul_pos t.primeQ.pos t.primeR.pos))⟩

theorem coprimePQ (t : Parameters) : t.p.Coprime t.q :=
  (Nat.coprime_primes t.primeP t.primeQ).mpr t.pq
theorem coprimePR (t : Parameters) : t.p.Coprime t.r :=
  (Nat.coprime_primes t.primeP t.primeR).mpr t.pr
theorem coprimeQR (t : Parameters) : t.q.Coprime t.r :=
  (Nat.coprime_primes t.primeQ t.primeR).mpr t.qr

noncomputable def coordinates (t : Parameters) : ZMod t.N ≃+* Site t.p t.q t.r :=
  ((ZMod.chineseRemainder (t.coprimePQ.mul_right t.coprimePR)).trans
    (RingEquiv.prodCongr (RingEquiv.refl (ZMod t.p))
      (ZMod.chineseRemainder t.coprimeQR))).trans
    (RingEquiv.prodCongr (ZMod.finEquiv t.p).symm
      (RingEquiv.prodCongr (ZMod.finEquiv t.q).symm (ZMod.finEquiv t.r).symm))

noncomputable def grid (t : Parameters) : ZMod t.N →+ UnitAddCircle := ZMod.toAddCircle

def sample (t : Parameters) (θ : Phase) (s : ZMod t.N) : Phase :=
  Phase.add θ (Phase.ofRat s.val t.N (Nat.pos_of_ne_zero (NeZero.ne _)))

theorem circle_sample (t : Parameters) (θ : Phase) (s : ZMod t.N) :
    circle (t.sample θ s) = circle θ + t.grid s := by
  rw [sample, circle_add]
  rw [grid, ZMod.toAddCircle_apply]
  rfl

def Elements (t : Parameters) (C : Config) : Prop :=
  ∀ i : Fin C.length, (C.get i).p = t.p ∨ (C.get i).p = t.q ∨ (C.get i).p = t.r

theorem element_dvd (t : Parameters) {e : ℕ} (he : e = t.p ∨ e = t.q ∨ e = t.r) :
    e ∣ t.N := by
  rcases he with rfl | rfl | rfl
  · exact dvd_mul_right _ _
  · exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  · exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _

theorem circle_point (t : Parameters) (A : Atom)
    (he : A.p = t.p ∨ A.p = t.q ∨ A.p = t.r) (j : Fin A.p) :
    circle (A.point j) = circle A.phase + t.grid ((t.N / A.p * j.val : ℕ) : ZMod t.N) := by
  rw [Atom.point, circle_add]
  congr 1
  rw [grid, ZMod.toAddCircle_natCast]
  change (((j.val : ℝ) / A.p : ℝ) : UnitAddCircle) = _
  congr 1
  have hmul : (t.N / A.p : ℕ) * A.p = t.N := Nat.div_mul_cancel (t.element_dvd he)
  have hN : (t.N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne t.N)
  have hp : (A.p : ℝ) ≠ 0 := by exact_mod_cast A.p_pos.ne'
  have hm : ((t.N / A.p : ℕ) : ℝ) * (A.p : ℝ) = t.N := by exact_mod_cast hmul
  push_cast
  field_simp
  nlinarith [hm]

theorem bond_difference (t : Parameters) {C : Config} (hC : t.Elements C)
    {i j : Fin C.length} (h : BondAdj C i j) :
    ∃ s : ZMod t.N, circle (C.get j).phase = circle (C.get i).phase + t.grid s := by
  obtain ⟨x, _, hi, hj⟩ := h
  obtain ⟨ki, hki⟩ := (hasPoint_iff_circle _ _).mp hi
  obtain ⟨kj, hkj⟩ := (hasPoint_iff_circle _ _).mp hj
  rw [t.circle_point _ (hC i)] at hki
  rw [t.circle_point _ (hC j)] at hkj
  refine ⟨(t.N / (C.get i).p * ki.val : ℕ) - (t.N / (C.get j).p * kj.val : ℕ), ?_⟩
  rw [map_sub]
  have hh := hki.symm.trans hkj
  exact (eq_sub_iff_add_eq.mpr hh.symm).trans (by abel)

theorem reachable_difference (t : Parameters) {C : Config} (hC : t.Elements C)
    {i j : Fin C.length} (h : BondReachable C i j) :
    ∃ s : ZMod t.N, circle (C.get j).phase = circle (C.get i).phase + t.grid s := by
  induction h with
  | refl i => exact ⟨0, by simp⟩
  | @step i j k hij _ ih =>
    obtain ⟨s, hs⟩ := t.bond_difference hC hij
    obtain ⟨u, hu⟩ := ih
    exact ⟨s + u, by rw [hu, hs, map_add, add_assoc]⟩

theorem alignment (t : Parameters) {C : Config} (hC : t.Elements C) (hc : IsConnected C) :
    ∃ θ : Phase, ∀ i : Fin C.length, ∃ s : ZMod t.N,
      circle (C.get i).phase = circle θ + t.grid s := by
  let root : Fin C.length := ⟨0, hc.1⟩
  exact ⟨(C.get root).phase, fun i => t.reachable_difference hC (hc.2 root i)⟩

def lineFor (t : Parameters) (e : ℕ) (s : Site t.p t.q t.r) : Line t.p t.q t.r :=
  if e = t.p then .pLine s.2.1 s.2.2
  else if e = t.q then .qLine s.1 s.2.2 else .rLine s.1 s.2.1

theorem lineFor_element (t : Parameters) (e : ℕ)
    (he : e = t.p ∨ e = t.q ∨ e = t.r) (s : Site t.p t.q t.r) :
    element (t.lineFor e s) = e := by
  rcases he with rfl | rfl | rfl <;>
    simp [lineFor, element, t.pq, t.pq.symm, t.pr.symm, t.qr.symm]

theorem periodP (t : Parameters) : t.N / t.p = t.q * t.r := by
  exact Nat.mul_div_cancel_left _ t.primeP.pos
theorem periodQ (t : Parameters) : t.N / t.q = t.p * t.r := by
  have h : t.N = t.q * (t.p * t.r) := by unfold N; ring
  rw [h, Nat.mul_div_cancel_left _ t.primeQ.pos]
theorem periodR (t : Parameters) : t.N / t.r = t.p * t.q := by
  have h : t.N = t.r * (t.p * t.q) := by unfold N; ring
  rw [h, Nat.mul_div_cancel_left _ t.primeR.pos]

theorem orbit_subset (t : Parameters) (e : ℕ)
    (he : e = t.p ∨ e = t.q ∨ e = t.r) (k : ZMod t.N) (j : Fin e) :
    covers (t.lineFor e (t.coordinates k))
      (t.coordinates (k + ((t.N / e * j.val : ℕ) : ZMod t.N))) := by
  rcases he with rfl | rfl | rfl
  all_goals simp only [map_add, map_natCast]
  · simp [lineFor, covers, t.periodP, Nat.cast_mul, t.pq, t.pr, t.qr]
  · simp [lineFor, covers, t.periodQ, Nat.cast_mul, t.pq.symm, t.pr, t.qr]
  · simp [lineFor, covers, t.periodR, Nat.cast_mul, t.pr.symm, t.qr.symm]

theorem fiber_card (t : Parameters) (e : ℕ)
    (he : e = t.p ∨ e = t.q ∨ e = t.r) (k : ZMod t.N) :
    (Finset.univ.filter (fun s : ZMod t.N =>
      covers (t.lineFor e (t.coordinates k)) (t.coordinates s))).card = e := by
  classical
  rcases he with rfl | rfl | rfl
  · conv_rhs => rw [← Finset.card_fin t.p]
    apply Finset.card_bij (fun s _ => (t.coordinates s).1)
    · simp
    · intro a ha b hb hab
      simp [lineFor, covers] at ha hb
      apply t.coordinates.injective
      exact Prod.ext hab (Prod.ext (ha.1.trans hb.1.symm) (ha.2.trans hb.2.symm))
    · intro x hx
      refine ⟨t.coordinates.symm (x, (t.coordinates k).2), ?_, ?_⟩ <;> simp [lineFor, covers]
  · conv_rhs => rw [← Finset.card_fin t.q]
    apply Finset.card_bij (fun s _ => (t.coordinates s).2.1)
    · simp
    · intro a ha b hb hab
      simp [lineFor, covers, t.pq.symm] at ha hb
      apply t.coordinates.injective
      exact Prod.ext (ha.1.trans hb.1.symm) (Prod.ext hab (ha.2.trans hb.2.symm))
    · intro y hy
      refine ⟨t.coordinates.symm ((t.coordinates k).1, y, (t.coordinates k).2.2), ?_, ?_⟩ <;>
        simp [lineFor, covers, t.pq.symm]
  · conv_rhs => rw [← Finset.card_fin t.r]
    apply Finset.card_bij (fun s _ => (t.coordinates s).2.2)
    · simp
    · intro a ha b hb hab
      simp [lineFor, covers, t.pr.symm, t.qr.symm] at ha hb
      apply t.coordinates.injective
      exact Prod.ext (ha.1.trans hb.1.symm) (Prod.ext (ha.2.trans hb.2.symm) hab)
    · intro z hz
      refine ⟨t.coordinates.symm ((t.coordinates k).1, (t.coordinates k).2.1, z), ?_, ?_⟩ <;>
        simp [lineFor, covers, t.pr.symm, t.qr.symm]

theorem orbit_injective (t : Parameters) (e : ℕ)
    (he : e = t.p ∨ e = t.q ∨ e = t.r) (k : ZMod t.N) :
    Function.Injective (fun j : Fin e => k + ((t.N / e * j.val : ℕ) : ZMod t.N)) := by
  have hepos : 0 < e := by rcases he with rfl | rfl | rfl <;> exact NeZero.pos _
  have hN : 0 < t.N := NeZero.pos _
  have hmul := Nat.div_mul_cancel (t.element_dvd he)
  have hperiod : 0 < t.N / e := Nat.div_pos (Nat.le_of_dvd hN (t.element_dvd he)) hepos
  intro i j hij
  apply Fin.ext
  have hi : t.N / e * i.val < t.N := by nlinarith [i.isLt]
  have hj : t.N / e * j.val < t.N := by nlinarith [j.isLt]
  have h := congrArg ZMod.val (add_left_cancel hij)
  rw [ZMod.val_cast_of_lt hi, ZMod.val_cast_of_lt hj] at h
  nlinarith

theorem orbit (t : Parameters) (e : ℕ)
    (he : e = t.p ∨ e = t.q ∨ e = t.r) (k s : ZMod t.N) :
    covers (t.lineFor e (t.coordinates k)) (t.coordinates s) ↔
      ∃ j : Fin e, s = k + ((t.N / e * j.val : ℕ) : ZMod t.N) := by
  classical
  let O := Finset.univ.image (fun j : Fin e => k + ((t.N / e * j.val : ℕ) : ZMod t.N))
  let F := Finset.univ.filter (fun s : ZMod t.N =>
    covers (t.lineFor e (t.coordinates k)) (t.coordinates s))
  have hsub : O ⊆ F := by
    intro s hs
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.orbit_subset e he k j⟩
  have hcard : O.card = F.card := by
    rw [Finset.card_image_of_injective _ (t.orbit_injective e he k), Finset.card_fin]
    exact (t.fiber_card e he k).symm
  have hEq := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  constructor
  · intro hs
    have hsF : s ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
    rw [← hEq] at hsF
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hsF
    exact ⟨j, hj.symm⟩
  · rintro ⟨j, rfl⟩
    exact t.orbit_subset e he k j

theorem aligned_atom_points (t : Parameters) (A : Atom)
    (he : A.p = t.p ∨ A.p = t.q ∨ A.p = t.r)
    (θ : Phase) (k : ZMod t.N) (hk : circle A.phase = circle θ + t.grid k)
    (x : Phase) :
    A.hasPoint x ↔ ∃ s : ZMod t.N,
      covers (t.lineFor A.p (t.coordinates k)) (t.coordinates s) ∧
      circle x = circle θ + t.grid s := by
  rw [hasPoint_iff_circle]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨k + ((t.N / A.p * j.val : ℕ) : ZMod t.N),
      (t.orbit A.p he _ _).mpr ⟨j, rfl⟩, ?_⟩
    rw [hj, t.circle_point A he, hk, map_add, add_assoc]
  · rintro ⟨s, hs, hx⟩
    obtain ⟨j, rfl⟩ := (t.orbit A.p he _ _).mp hs
    refine ⟨j, ?_⟩
    rw [hx, t.circle_point A he, hk, map_add, add_assoc]

structure Alignment (t : Parameters) (C : Config) where
  origin : Phase
  lines : Fin C.length → Line t.p t.q t.r
  element_eq : ∀ i, element (lines i) = (C.get i).p
  points : ∀ i x, (C.get i).hasPoint x ↔ ∃ s : ZMod t.N,
    covers (lines i) (t.coordinates s) ∧ circle x = circle origin + t.grid s

theorem molecule_alignment (t : Parameters) {C : Config} (hC : t.Elements C)
    (hm : IsMolecule C) : Nonempty (Alignment t C) := by
  obtain ⟨θ, hθ⟩ := t.alignment hC hm.connected
  choose k hk using hθ
  exact ⟨{
    origin := θ
    lines := fun i => t.lineFor (C.get i).p (t.coordinates (k i))
    element_eq := fun i => t.lineFor_element _ (hC i) _
    points := fun i x => t.aligned_atom_points _ (hC i) θ (k i) (hk i) x
  }⟩

theorem Alignment.at_sample {t : Parameters} {C : Config} (g : Alignment t C)
    (i : Fin C.length) (s : ZMod t.N) :
    (C.get i).hasPoint (t.sample g.origin s) ↔ covers (g.lines i) (t.coordinates s) := by
  rw [g.points]
  constructor
  · rintro ⟨u, hu, heq⟩
    rw [t.circle_sample, add_left_cancel_iff] at heq
    have hsu := ZMod.toAddCircle_injective t.N heq
    simpa [hsu] using hu
  · intro hs
    exact ⟨s, hs, t.circle_sample g.origin s⟩

def anchor {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] : Line p q r → Site p q r
  | .pLine y z => (0, y, z)
  | .qLine x z => (x, 0, z)
  | .rLine x y => (x, y, 0)

noncomputable def lineAtom (t : Parameters) (l : Line t.p t.q t.r) : Atom :=
  ⟨element l, Phase.ofRat (t.coordinates.symm (anchor l)).val t.N (NeZero.pos _), by
    cases l <;> simp only [element]
    · exact t.primeP.two_le
    · exact t.primeQ.two_le
    · exact t.primeR.two_le⟩

theorem lineAtom_points (t : Parameters) (l : Line t.p t.q t.r) (x : Phase) :
    (t.lineAtom l).hasPoint x ↔ ∃ s : ZMod t.N,
      covers l (t.coordinates s) ∧ circle x = t.grid s := by
  have he : (t.lineAtom l).p = t.p ∨ (t.lineAtom l).p = t.q ∨
      (t.lineAtom l).p = t.r := by cases l <;> simp [lineAtom, element]
  have hk : circle (t.lineAtom l).phase =
      circle Phase.zero + t.grid (t.coordinates.symm (anchor l)) := by
    rw [grid, ZMod.toAddCircle_apply]
    simp [lineAtom, circle, Phase.zero, Phase.ofRat]
  have hl : t.lineFor (t.lineAtom l).p (anchor l) = l := by
    cases l <;> simp [lineFor, lineAtom, element, anchor, t.pq.symm, t.pr.symm, t.qr.symm]
  have h := t.aligned_atom_points (t.lineAtom l) he Phase.zero _ hk x
  simpa only [RingEquiv.apply_symm_apply, hl, circle, Phase.zero, Nat.cast_zero,
    Nat.cast_one, zero_div, AddCircle.coe_zero, zero_add] using h

end Parameters
end CyclicAtoms.PrimeGeometry
