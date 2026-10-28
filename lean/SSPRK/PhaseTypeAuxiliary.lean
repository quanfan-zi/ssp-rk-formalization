import SSPRK.AuxiliaryLaw
import SSPRK.MomentConvolution
import SSPRK.PhaseTypeReturn
import SSPRK.PhaseTypeTimeChange

/-!
# Independent three-moment replacement of a PH time

After normalizing one Green diagonal entry, the smaller PH law and an independent
nonnegative auxiliary variable reproduce the first three moments of the original
fixed-state law. This constructs the replacement in historical V1.6 Lemma 4.5 as a convolution
of actual probability measures; it does not identify actual occupation times as independent.
-/

open MeasureTheory

namespace SSPRK.PhaseTypeData

/-- The normalized PH law has the first three moments of an independent smaller-law sum. -/
theorem normalized_independent_replacement {n : ℕ} (d : PhaseTypeData (n + 1)) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ (∀ᵐ x ∂μ, 0 ≤ x) ∧
      (∀ k : ℕ, Integrable (fun x : ℝ ↦ x ^ k) μ) ∧
      MomentClass 1 (∫ x, x ∂μ) (∫ x, x ^ 2 ∂μ) (∫ x, x ^ 3 ∂μ) ∧
      Integrable (fun x : ℝ ↦ x) (independentSumLaw d.normalizedTail.measure μ) ∧
      Integrable (fun x : ℝ ↦ x ^ 2) (independentSumLaw d.normalizedTail.measure μ) ∧
      Integrable (fun x : ℝ ↦ x ^ 3) (independentSumLaw d.normalizedTail.measure μ) ∧
      (∫ x, x ∂independentSumLaw d.normalizedTail.measure μ) =
        (∫ x, x ∂d.normalizedStart.measure) ∧
      (∫ x, x ^ 2 ∂independentSumLaw d.normalizedTail.measure μ) =
        (∫ x, x ^ 2 ∂d.normalizedStart.measure) ∧
      (∫ x, x ^ 3 ∂independentSumLaw d.normalizedTail.measure μ) =
        (∫ x, x ^ 3 ∂d.normalizedStart.measure) := by
  obtain ⟨μ, hprob, hnonneg, hint, hfirst, hsecond, hthird⟩ :=
    exists_auxiliary_probability (phaseBlockEta1 d.normalizedGreen)
      (phaseBlockEta2 d.normalizedGreen) d.normalizedGreen_eta1_nonneg
      (d.normalizedGreen_eta2_nonneg d.normalizedGreen_blockH_nonneg)
      (d.normalized_green_eta2_eq_zero)
  have hμ1 : Integrable (fun x : ℝ ↦ x) μ := by simpa only [pow_one] using hint 1
  have h1 := independentSumLaw_first_moment d.normalizedTail.measure μ
    d.normalizedTail.integrable_id_measure hμ1
  have h2 := independentSumLaw_second_moment d.normalizedTail.measure μ
    d.normalizedTail.integrable_id_measure hμ1 d.normalizedTail.integrable_sq_measure (hint 2)
  have h3 := independentSumLaw_third_moment d.normalizedTail.measure μ
    d.normalizedTail.integrable_id_measure hμ1 d.normalizedTail.integrable_sq_measure (hint 2)
    (d.normalizedTail.integrable_pow_measure 3) (hint 3)
  refine ⟨μ, hprob, hnonneg, hint, ?_, h1.1, h2.1, h3.1, ?_, ?_, ?_⟩
  · rw [hfirst, hsecond, hthird]
    exact auxiliary_moment_class d.normalizedGreen_eta1_nonneg
      (d.normalizedGreen_eta2_nonneg d.normalizedGreen_blockH_nonneg)
  · rw [h1.2, hfirst, d.normalizedTail_integral_one, d.normalizedStart_integral_one,
      phaseBlock_first_moment _ d.normalizedGreen_zero_zero]
  · rw [h2.2, hfirst, hsecond, d.normalizedTail_integral_one,
      d.normalizedTail_integral_two, d.normalizedStart_integral_two,
      phaseBlock_second_moment _ d.normalizedGreen_zero_zero]
    ring
  · rw [h3.2, hfirst, hsecond, hthird, d.normalizedTail_integral_one,
      d.normalizedTail_integral_two, d.normalizedTail_integral_three,
      d.normalizedStart_integral_three, phaseBlock_third_moment _ d.normalizedGreen_zero_zero]
    ring

end SSPRK.PhaseTypeData
