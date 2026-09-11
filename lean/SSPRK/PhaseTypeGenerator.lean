import SSPRK.PhaseTypeData

/-!
# Continuous Green matrices for phase-type data

The continuous occupation matrix is the inverse negative generator. Uniformization scales it by
the reciprocal clock rate.
-/

open scoped BigOperators

namespace SSPRK.PhaseTypeData

variable {s : ℕ} (d : PhaseTypeData s)

/-- The continuous Green matrix, equal to the inverse negative transient generator. -/
noncomputable def continuousGreen : Matrix (Fin s) (Fin s) ℝ := (-d.generator)⁻¹

theorem neg_generator : -d.generator = d.rate • (1 - d.transition) := by
  unfold generator
  module

theorem continuousGreen_eq : d.continuousGreen = d.rate⁻¹ • d.green := by
  letI : Invertible d.rate := invertibleOfNonzero (ne_of_gt d.rate_pos)
  rw [continuousGreen, d.neg_generator, Matrix.inv_smul (1 - d.transition) d.rate]
  · simp only [invOf_eq_inv, green]
  · exact isUnit_iff_ne_zero.mpr d.transient

theorem continuousGreen_pow (k : ℕ) : d.continuousGreen ^ k = d.rate⁻¹ ^ k • d.green ^ k := by
  rw [d.continuousGreen_eq]
  exact smul_pow _ _ _

theorem dotProduct_continuousGreen_pow (k : ℕ) :
    dotProduct d.initial ((d.continuousGreen ^ k).mulVec (fun _ ↦ 1)) =
      dotProduct d.initial ((d.green ^ k).mulVec (fun _ ↦ 1)) / d.rate ^ k := by
  rw [d.continuousGreen_pow, Matrix.smul_mulVec, dotProduct_smul, div_eq_mul_inv, ← inv_pow]
  ring

end SSPRK.PhaseTypeData
