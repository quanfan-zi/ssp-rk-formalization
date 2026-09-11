import SSPRK.PhaseTypeMoments
import SSPRK.PhaseMomentBound
import Mathlib.Probability.Moments.Variance

/-!
# Minimum variance of a finite phase-type law

Theorem 3.1 of V1.6 for the probability measure constructed by uniformization.
Initial mixtures and an atom at zero are included.
-/

open MeasureTheory

namespace SSPRK.PhaseTypeData

variable {s : ℕ} (d : PhaseTypeData s)

/-- The phase-count lower bound, expressed using genuine integrals of the PH measure. -/
theorem second_moment_lower_bound (hs : 0 < s) :
    ((s : ℝ) + 1) * (∫ x, x ∂d.measure) ^ 2 ≤ (s : ℝ) * ∫ x, x ^ 2 ∂d.measure := by
  have hleft : (1 - d.transition) * d.green = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr d.transient)
  have hright : d.green * (1 - d.transition) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr d.transient)
  have hbound := phase_second_moment_bound s hs d.transition d.green d.initial
    d.substochastic (d.substochastic.inv_nonneg d.transient) hleft hright
    d.initial_nonneg d.initial_mass_le
  rw [d.integral_id_measure, d.integral_sq_measure]
  calc
    _ = (((s : ℝ) + 1) * (dotProduct d.initial (d.green.mulVec (fun _ ↦ 1))) ^ 2) /
        d.rate ^ 2 := by ring
    _ ≤ (2 * (s : ℝ) * dotProduct d.initial
        (d.green.mulVec (d.green.mulVec (fun _ ↦ 1)))) / d.rate ^ 2 :=
      div_le_div_of_nonneg_right hbound (sq_nonneg _)
    _ = _ := by ring

/-- The absorption-time variance is its second Green moment minus the square of its mean. -/
theorem variance_measure :
    ProbabilityTheory.variance (fun x : ℝ ↦ x) d.measure =
      (∫ x, x ^ 2 ∂d.measure) - (∫ x, x ∂d.measure) ^ 2 := by
  exact ProbabilityTheory.variance_eq_sub
    ((memLp_two_iff_integrable_sq (by fun_prop)).mpr d.integrable_sq_measure)

/-- Aldous--Shepp's minimum-variance inequality, including mixtures and a zero atom. -/
theorem variance_lower_bound (hs : 0 < s) :
    (∫ x, x ∂d.measure) ^ 2 / (s : ℝ) ≤
      ProbabilityTheory.variance (fun x : ℝ ↦ x) d.measure := by
  apply (div_le_iff₀ (Nat.cast_pos.mpr hs)).mpr
  rw [d.variance_measure]
  nlinarith [d.second_moment_lower_bound hs]

end SSPRK.PhaseTypeData
