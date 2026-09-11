import SSPRK.LengthBias
import SSPRK.MomentConvolution

/-!
# Length bias of an independent sum

Equation (4.8) is an equality of probability laws: length bias chooses which summand
to bias, with probabilities proportional to the two means.
-/

open MeasureTheory
open scoped ENNReal

namespace SSPRK

lemma withDensity_map_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (g : α → β) (f : β → ℝ≥0∞) (hg : Measurable g) (hf : Measurable f) :
    (μ.map g).withDensity f = (μ.withDensity (fun x ↦ f (g x))).map g := by
  refine Measure.ext_of_lintegral _ fun φ hφ ↦ ?_
  rw [lintegral_withDensity_eq_lintegral_mul _ hf hφ]
  simp only [Pi.mul_apply]
  rw [lintegral_map (hf.mul hφ) hg, lintegral_map hφ hg]
  exact (lintegral_withDensity_eq_lintegral_mul μ (hf.comp hg) (hφ.comp hg)).symm

theorem lengthBias_independentSumLaw (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (hν : ∀ᵐ y ∂ν, 0 ≤ y)
    (hintμ : Integrable (fun x : ℝ ↦ x) μ) (hintν : Integrable (fun x : ℝ ↦ x) ν)
    (hx : 0 < ∫ x, x ∂μ) (hy : 0 < ∫ y, y ∂ν) :
    lengthBias (independentSumLaw μ ν) =
      ENNReal.ofReal ((∫ x, x ∂μ) / ((∫ x, x ∂μ) + ∫ y, y ∂ν)) •
        independentSumLaw (lengthBias μ) ν +
      ENNReal.ofReal ((∫ y, y ∂ν) / ((∫ x, x ∂μ) + ∫ y, y ∂ν)) •
        independentSumLaw μ (lengthBias ν) := by
  let x : ℝ := ∫ t, t ∂μ
  let y : ℝ := ∫ t, t ∂ν
  have hx' : 0 < x := hx
  have hy' : 0 < y := hy
  have hxy : 0 < x + y := add_pos hx' hy'
  have hmean : (∫ z, z ∂independentSumLaw μ ν) = x + y :=
    (independentSumLaw_first_moment μ ν hintμ hintν).2
  have hnonneg : ∀ᵐ z : ℝ × ℝ ∂μ.prod ν, 0 ≤ z.1 ∧ 0 ≤ z.2 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
    filter_upwards [hμ] with a ha
    filter_upwards [hν] with b hb
    exact ⟨ha, hb⟩
  have hdensity : (fun z : ℝ × ℝ ↦ ENNReal.ofReal ((z.1 + z.2) / (x + y))) =ᵐ[μ.prod ν]
      (fun z ↦ ENNReal.ofReal (x / (x + y)) * ENNReal.ofReal (z.1 / x) +
        ENNReal.ofReal (y / (x + y)) * ENNReal.ofReal (z.2 / y)) := by
    filter_upwards [hnonneg] with z hz
    rw [← ENNReal.ofReal_mul (div_nonneg hx'.le hxy.le),
      ← ENNReal.ofReal_mul (div_nonneg hy'.le hxy.le)]
    rw [← ENNReal.ofReal_add
      (mul_nonneg (div_nonneg hx'.le hxy.le) (div_nonneg hz.1 hx'.le))
      (mul_nonneg (div_nonneg hy'.le hxy.le) (div_nonneg hz.2 hy'.le))]
    congr 1
    field_simp
  have hprod : (μ.prod ν).withDensity
      (fun z : ℝ × ℝ ↦ ENNReal.ofReal ((z.1 + z.2) / (x + y))) =
      ENNReal.ofReal (x / (x + y)) • (lengthBias μ).prod ν +
      ENNReal.ofReal (y / (x + y)) • μ.prod (lengthBias ν) := by
    rw [withDensity_congr_ae hdensity]
    change (μ.prod ν).withDensity
      (ENNReal.ofReal (x / (x + y)) • (fun z : ℝ × ℝ ↦ ENNReal.ofReal (z.1 / x)) +
        ENNReal.ofReal (y / (x + y)) • (fun z : ℝ × ℝ ↦ ENNReal.ofReal (z.2 / y))) = _
    rw [withDensity_add_left (by fun_prop), withDensity_smul _ (by fun_prop),
      withDensity_smul _ (by fun_prop)]
    rw [lengthBias, lengthBias,
      prod_withDensity_left (f := fun t : ℝ ↦ ENNReal.ofReal (t / x)) (by fun_prop),
      prod_withDensity_right (g := fun t : ℝ ↦ ENNReal.ofReal (t / y)) (by fun_prop)]
  rw [lengthBias, hmean, independentSumLaw_eq_map,
    withDensity_map_comp _ _ _ (by fun_prop) (by fun_prop)]
  rw [hprod, Measure.map_add _ _ (by fun_prop), Measure.map_smul, Measure.map_smul]
  rfl

end SSPRK
