import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-!
# The length-biased probability law

Weighting a nonnegative law by its value and dividing by its mean defines an actual
probability measure. Its first two moments and normalized variance give Equation (4.3).
-/

open MeasureTheory

namespace SSPRK

noncomputable def lengthBias (μ : Measure ℝ) : Measure ℝ :=
  μ.withDensity (fun x ↦ ENNReal.ofReal (x / ∫ t, t ∂μ))

theorem lengthBias_probability (μ : Measure ℝ) (hμ : ∀ᵐ x ∂μ, 0 ≤ x)
    (hint : Integrable (fun x : ℝ ↦ x) μ) (hm : 0 < ∫ x, x ∂μ) :
    IsProbabilityMeasure (lengthBias μ) := by
  constructor
  rw [lengthBias, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.div_const (∫ x, x ∂μ))
    (hμ.mono fun x hx ↦ div_nonneg hx hm.le)]
  simp only [div_eq_mul_inv, integral_mul_const]
  rw [mul_inv_cancel₀ (ne_of_gt hm), ENNReal.ofReal_one]

theorem lengthBias_ae_nonneg (μ : Measure ℝ) (hμ : ∀ᵐ x ∂μ, 0 ≤ x) :
    ∀ᵐ x ∂lengthBias μ, 0 ≤ x :=
  (withDensity_absolutelyContinuous μ _).ae_le hμ

@[simp] theorem lengthBias_zero_atom (μ : Measure ℝ) : lengthBias μ {0} = 0 := by
  rw [lengthBias, withDensity_apply _ (measurableSet_singleton 0)]
  simp

theorem lengthBias_integral (μ : Measure ℝ) (hμ : ∀ᵐ x ∂μ, 0 ≤ x)
    (hm : 0 < ∫ x, x ∂μ) (f : ℝ → ℝ) :
    (∫ x, f x ∂lengthBias μ) = (∫ x, x * f x ∂μ) / ∫ x, x ∂μ := by
  rw [lengthBias, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ fun x ↦ ENNReal.ofReal_lt_top)]
  calc
    _ = ∫ x, (x * f x) / (∫ t, t ∂μ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hμ] with x hx
      rw [ENNReal.toReal_ofReal (div_nonneg hx hm.le), smul_eq_mul]
      ring
    _ = _ := by simp only [div_eq_mul_inv, integral_mul_const]

theorem lengthBias_integrable (μ : Measure ℝ) (hμ : ∀ᵐ x ∂μ, 0 ≤ x)
    (hm : 0 < ∫ x, x ∂μ) (f : ℝ → ℝ) (hf : Integrable (fun x ↦ x * f x) μ) :
    Integrable f (lengthBias μ) := by
  rw [lengthBias, integrable_withDensity_iff (by fun_prop)
    (ae_of_all _ fun x ↦ ENNReal.ofReal_lt_top)]
  apply (hf.div_const (∫ x, x ∂μ)).congr
  filter_upwards [hμ] with x hx
  rw [ENNReal.toReal_ofReal (div_nonneg hx hm.le)]
  ring

theorem lengthBias_first_moment (μ : Measure ℝ) (hμ : ∀ᵐ x ∂μ, 0 ≤ x)
    (hm : 0 < ∫ x, x ∂μ) (h2 : Integrable (fun x : ℝ ↦ x ^ 2) μ) :
    Integrable (fun x : ℝ ↦ x) (lengthBias μ) ∧
      (∫ x, x ∂lengthBias μ) = (∫ x, x ^ 2 ∂μ) / ∫ x, x ∂μ := by
  refine ⟨lengthBias_integrable μ hμ hm _ (by simpa only [pow_two] using h2), ?_⟩
  simpa only [pow_two] using lengthBias_integral μ hμ hm (fun x ↦ x)

theorem lengthBias_second_moment (μ : Measure ℝ) (hμ : ∀ᵐ x ∂μ, 0 ≤ x)
    (hm : 0 < ∫ x, x ∂μ) (h3 : Integrable (fun x : ℝ ↦ x ^ 3) μ) :
    Integrable (fun x : ℝ ↦ x ^ 2) (lengthBias μ) ∧
      (∫ x, x ^ 2 ∂lengthBias μ) = (∫ x, x ^ 3 ∂μ) / ∫ x, x ∂μ := by
  refine ⟨lengthBias_integrable μ hμ hm _ (by simpa only [← pow_succ'] using h3), ?_⟩
  calc
    _ = (∫ x, x * x ^ 2 ∂μ) / (∫ x, x ∂μ) := lengthBias_integral μ hμ hm _
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ fun x ↦ by ring

theorem lengthBias_variance (μ : Measure ℝ) (hμ : ∀ᵐ x ∂μ, 0 ≤ x)
    (h1 : Integrable (fun x : ℝ ↦ x) μ) (hm : 0 < ∫ x, x ∂μ)
    (h2 : Integrable (fun x : ℝ ↦ x ^ 2) μ) (h3 : Integrable (fun x : ℝ ↦ x ^ 3) μ) :
    ProbabilityTheory.variance (fun x : ℝ ↦ x) (lengthBias μ) =
      (∫ x, x ^ 3 ∂μ) / (∫ x, x ∂μ) - ((∫ x, x ^ 2 ∂μ) / (∫ x, x ∂μ)) ^ 2 := by
  letI : IsProbabilityMeasure (lengthBias μ) := lengthBias_probability μ hμ h1 hm
  have hsecond := lengthBias_second_moment μ hμ hm h3
  have hfirst := lengthBias_first_moment μ hμ hm h2
  have hl2 : MemLp (fun x : ℝ ↦ x) 2 (lengthBias μ) := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).2
    exact hsecond.1
  rw [ProbabilityTheory.variance_eq_sub hl2]
  simp only [Pi.pow_apply]
  rw [hsecond.2, hfirst.2]

theorem lengthBias_mean_pos (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (hm : 0 < ∫ x, x ∂μ)
    (h2 : Integrable (fun x : ℝ ↦ x ^ 2) μ) : 0 < ∫ x, x ∂lengthBias μ := by
  have hl2 : MemLp (fun x : ℝ ↦ x) 2 μ :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 h2
  have hv := ProbabilityTheory.variance_nonneg (fun x : ℝ ↦ x) μ
  rw [ProbabilityTheory.variance_eq_sub hl2] at hv
  simp only [Pi.pow_apply] at hv
  rw [(lengthBias_first_moment μ hμ hm h2).2]
  exact div_pos (by nlinarith [sq_pos_of_pos hm]) hm

/-- Equation (4.3): the second normalized moment ratio is the squared coefficient of variation
of the length-biased law, plus one. -/
theorem lengthBias_normalized_variance (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (h1 : Integrable (fun x : ℝ ↦ x) μ)
    (hm : 0 < ∫ x, x ∂μ) (h2 : Integrable (fun x : ℝ ↦ x ^ 2) μ)
    (h3 : Integrable (fun x : ℝ ↦ x ^ 3) μ) :
    (∫ x, x ∂μ) * (∫ x, x ^ 3 ∂μ) / (∫ x, x ^ 2 ∂μ) ^ 2 - 1 =
      ProbabilityTheory.variance (fun x : ℝ ↦ x) (lengthBias μ) /
        (∫ x, x ∂lengthBias μ) ^ 2 := by
  have hpos := lengthBias_mean_pos μ hμ hm h2
  rw [(lengthBias_first_moment μ hμ hm h2).2] at hpos
  have hsecond : (∫ x, x ^ 2 ∂μ) ≠ 0 := by
    intro hz
    rw [hz, zero_div] at hpos
    exact (lt_irrefl 0) hpos
  rw [lengthBias_variance μ hμ h1 hm h2 h3, (lengthBias_first_moment μ hμ hm h2).2]
  field_simp

end SSPRK
