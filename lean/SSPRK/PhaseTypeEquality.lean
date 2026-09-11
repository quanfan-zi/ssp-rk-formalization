import SSPRK.PhaseTypeVariance
import SSPRK.PhaseMixtureChain

/-!
# Equality conditions for the PH variance bound

The probability-law equality is equivalent to the algebraic Green-moment equality.
The positive clock rate cancels from this condition.
-/

open MeasureTheory

namespace SSPRK.PhaseTypeData

variable {s : ℕ} (d : PhaseTypeData s)

/-- Variance equality is unchanged by the uniformizing time scale. -/
theorem variance_eq_iff_green_moments (hs : 0 < s) :
    ProbabilityTheory.variance (fun x : ℝ ↦ x) d.measure =
        (∫ x, x ∂d.measure) ^ 2 / (s : ℝ) ↔
      ((s : ℝ) + 1) * (dotProduct d.initial (d.green.mulVec (fun _ ↦ 1))) ^ 2 =
        2 * (s : ℝ) *
          dotProduct d.initial (d.green.mulVec (d.green.mulVec (fun _ ↦ 1))) := by
  rw [d.variance_measure, d.integral_id_measure, d.integral_sq_measure]
  field_simp [ne_of_gt d.rate_pos, ne_of_gt (Nat.cast_pos.mpr hs : 0 < (s : ℝ))]
  constructor <;> intro h <;> nlinarith only [h]

/-- Variance equality forces a single initial state and an equal-rate generator chain. -/
theorem variance_equality_representation (hs : 0 < s)
    (hmean : 0 < ∫ x, x ∂d.measure)
    (heq : ProbabilityTheory.variance (fun x : ℝ ↦ x) d.measure =
      (∫ x, x ∂d.measure) ^ 2 / (s : ℝ)) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ e : Fin s ≃ Fin s,
      d.generator.submatrix e e = -κ • chainD s ∧
      (∀ j, d.initial (e j) = if j = ⟨s - 1, by omega⟩ then 1 else 0) := by
  have hleft : (1 - d.transition) * d.green = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr d.transient)
  have hright : d.green * (1 - d.transition) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr d.transient)
  have hmean' : 0 < dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)) :=
    (div_pos_iff_of_pos_right d.rate_pos).mp (by rwa [d.integral_id_measure] at hmean)
  obtain ⟨a, ha, e, hPform, _, hinitial, _⟩ :=
    phase_mixture_chain_classification_of_pos hs d.transition d.green d.initial
      d.substochastic (d.substochastic.inv_nonneg d.transient) hleft hright
      d.initial_nonneg d.initial_mass_le hmean' ((d.variance_eq_iff_green_moments hs).mp heq)
  refine ⟨d.rate / a, div_pos d.rate_pos ha, e, ?_, hinitial⟩
  have hgen : d.generator.submatrix e e = d.rate • (d.transition.submatrix e e - 1) := by
    ext j k
    simp [generator, Matrix.submatrix, Matrix.one_apply]
  rw [hgen, hPform, div_eq_mul_inv]
  module

end SSPRK.PhaseTypeData
