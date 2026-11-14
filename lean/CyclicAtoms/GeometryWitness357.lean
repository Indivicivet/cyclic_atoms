import CyclicAtoms.GeometryWitnessData

namespace CyclicAtoms.Geometry

open Chemistry

def witnessConfig357 (i : Fin 86) : Config :=
  realizeLines (gridWitnesses357.getD i.val [])

def treeCertificate357 (i : Fin 86) : TreeCertificate :=
  treeCertificates357.getD i.val ⟨[], []⟩

/-- Independently check occupancy and spanning trees for the actual circle witnesses. -/
theorem geometric_witness_checks357 : ∀ i : Fin 86,
    FinitePairing (canonicalAlignment (gridWitnesses357.getD i.val [])) ∧
    TreeCondition (canonicalAlignment (gridWitnesses357.getD i.val []))
      (treeCertificate357 i) := by native_decide

theorem witness_isMolecule357 (i : Fin 86) : IsMolecule (witnessConfig357 i) :=
  (canonicalAlignment _).isMolecule (geometric_witness_checks357 i).1
    (treeCertificate357 i) (geometric_witness_checks357 i).2

theorem witness_elements357 (i : Fin 86) : Elements357 (witnessConfig357 i) :=
  realizeLines_elements _

theorem witness_formula357 (i : Fin 86) :
    configFormula (witnessConfig357 i) = formula357 i :=
  (realizeLines_formula _).trans (catalog_witnesses357 i).2

/-- The complete catalog consists of original `IsMolecule` configurations. -/
theorem catalog_realizable357 (m : Formula) (hm : m ∈ formulas357) :
    ∃ C : Config, IsMolecule C ∧ Elements357 C ∧ configFormula C = m := by
  have hi : ∃ i : Fin 86, formula357 i = m := by
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
    have hib : i.val < 86 := by simpa only [catalog_length357] using i.isLt
    refine ⟨⟨i.val, hib⟩, ?_⟩
    simpa [formula357, formulaAt357, i.isLt, List.get_eq_getElem] using hi
  obtain ⟨i, rfl⟩ := hi
  exact ⟨witnessConfig357 i, witness_isMolecule357 i, witness_elements357 i,
    witness_formula357 i⟩

end CyclicAtoms.Geometry
