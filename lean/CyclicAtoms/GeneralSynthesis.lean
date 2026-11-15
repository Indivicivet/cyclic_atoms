import CyclicAtoms.OriginalClassification
import CyclicAtoms.PrimeMoleculeWitness
import CyclicAtoms.MolecularSynthesis

namespace CyclicAtoms.GeneralSynthesis

open UniversalSynthesis PrimeGeometry

theorem elements_iff (t : Parameters) (C : Config) :
    t.Elements C ↔ Elements t.p t.q t.r C := by
  constructor
  · intro h a ha
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    exact h i
  · intro h i
    exact h _ (List.get_mem C i)

/-- `Valid` is equivalent to existence of an original geometric molecule
with that formula; it is not a replacement definition of `IsMolecule`. -/
theorem valid_iff_original_molecule (t : Parameters) (f : Formula) :
    Valid t.p t.q t.r f ↔
      ∃ C : Config, IsMolecule C ∧ Elements t.p t.q t.r C ∧
        configFormula t.p t.q t.r C = f := by
  constructor
  · intro hf
    obtain ⟨C, hm, he, hformula⟩ := t.every_valid_realizable hf
    exact ⟨C, hm, (elements_iff t C).mp he, hformula⟩
  · rintro ⟨C, hm, he, hformula⟩
    rw [← hformula]
    exact t.original_molecule_valid C hm ((elements_iff t C).mpr he)

/-- Every original molecule over three distinct primes can be produced
from any two binary feed species. All stock entries are original molecules;
each event consumes two copies and produces two copies, conserving every
element. The requested geometric configuration itself occurs in the result. -/
theorem every_molecule_with_elements (p q r : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (C : Config) (hm : IsMolecule C)
    (helements : ∀ e : ℕ, C.HasElement e → e = p ∨ e = q ∨ e = r)
    (pair : Fin 3) :
    ∃ initial final : Multiset (Molecule p q r),
      (∀ m ∈ initial, m.formula ∈ feedPair p q r pair) ∧
      MolecularChain p q r initial final ∧ ∃ m ∈ final, m.config = C := by
  let t : Parameters := ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩
  have hC : Elements p q r C := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    exact helements _ ⟨i, rfl⟩
  have hclassify : ∀ m : Molecule p q r, Valid p q r m.formula := by
    intro m
    exact (valid_iff_original_molecule t m.formula).mpr
      ⟨m.config, m.molecule, m.elements, rfl⟩
  have hrealize : ∀ f : Formula, Valid p q r f → ∃ m : Molecule p q r, m.formula = f := by
    intro f hf
    obtain ⟨D, hD, heD, hformula⟩ := (valid_iff_original_molecule t f).mp hf
    exact ⟨⟨D, hD, heD⟩, hformula⟩
  obtain ⟨initial, final, hi, hc, ht⟩ :=
    synthesis_of_classification_and_realization p q r hp.two_le hq.two_le hr.two_le
      hpq hpr hqr hclassify hrealize ⟨C, hm, hC⟩ pair
  exact ⟨initial, final, hi, hc, ⟨⟨C, hm, hC⟩, ht, rfl⟩⟩

/-- info: 'CyclicAtoms.GeneralSynthesis.valid_iff_original_molecule' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms valid_iff_original_molecule

/-- info: 'CyclicAtoms.GeneralSynthesis.every_molecule_with_elements' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms every_molecule_with_elements

end CyclicAtoms.GeneralSynthesis
