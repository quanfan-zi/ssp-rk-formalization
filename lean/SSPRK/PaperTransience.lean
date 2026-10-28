import SSPRK.ErlangUniformizedWeights
import SSPRK.PhaseTypeAbsorptionLaw

/-!
# Transient subintensity matrices and actual absorption

The algebraic criterion in Proposition 2.3 is equivalent to the existence of a
uniformized representation for every initial subprobability row. The constructed
canonical process absorbs in finite time almost surely, including when started
from any individual transient state. No probability law is postulated as an axiom.
-/

open MeasureTheory
open scoped BigOperators

namespace SSPRK

/-- The sign of the whole matrix does not affect nonsingularity. -/
theorem matrix_det_neg_ne_zero_iff {s : ℕ} (T : Matrix (Fin s) (Fin s) ℝ) :
    (-T).det ≠ 0 ↔ T.det ≠ 0 := by
  simp [Matrix.det_neg]

/-- The explicit subintensity criterion constructs the canonical absorbing process. -/
theorem exists_absorbing_phaseType_of_generator_conditions {s : ℕ}
    (T : Matrix (Fin s) (Fin s) ℝ)
    (hoff : ∀ i j, i ≠ j → 0 ≤ T i j) (hrow : ∀ i, ∑ j, T i j ≤ 0)
    (hdet : T.det ≠ 0) (α : Fin s → ℝ) (hα : ∀ i, 0 ≤ α i)
    (hmass : ∑ i, α i ≤ 1) :
    ∃ d : PhaseTypeData s, d.generator = T ∧ d.initial = α ∧
      (∀ᵐ records ∂d.canonicalRecords, PhaseTypeData.recordAbsorptionTime records ≠ ⊤) := by
  let hT : FiniteSubgenerator T :=
    ⟨hoff, hrow, (matrix_det_neg_ne_zero_iff T).2 hdet⟩
  let d := hT.uniformizeCanonical α hα hmass
  exact ⟨d, hT.generator_uniformizeCanonical α hα hmass, rfl,
    d.canonicalRecords_absorptionTime_ne_top_ae⟩

/-- Every transient generator realized by phase-type data satisfies the matrix criterion. -/
theorem generator_conditions_of_phaseType {s : ℕ} (d : PhaseTypeData s) :
    (∀ i j, i ≠ j → 0 ≤ d.generator i j) ∧
      (∀ i, ∑ j, d.generator i j ≤ 0) ∧ d.generator.det ≠ 0 := by
  exact ⟨d.generator_finiteSubgenerator.offdiag_nonneg,
    d.generator_finiteSubgenerator.row_sum_nonpos,
    (matrix_det_neg_ne_zero_iff d.generator).1
      d.generator_finiteSubgenerator.det_neg_ne_zero⟩

end SSPRK
