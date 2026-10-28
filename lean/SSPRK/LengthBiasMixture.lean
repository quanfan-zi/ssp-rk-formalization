import SSPRK.LengthBias
import SSPRK.ProbabilityMomentMixture

/-!
# Length bias of a countable mixture

Length bias reweights each component by its mean. The residual atom at zero disappears,
and the resulting component weights sum to one. Only first moments are required.
-/

open MeasureTheory
open scoped ENNReal

namespace SSPRK

/-- The completed mixture has the weighted component mean, assuming only first moments. -/
theorem probabilityMomentMixture_first_moment (π : ℕ → ℝ) (μ : ℕ → Measure ℝ)
    (hπ : ∀ i, 0 ≤ π i) (hnonneg : ∀ i, ∀ᵐ t ∂μ i, 0 ≤ t)
    (hint : ∀ i, Integrable (fun t : ℝ ↦ t) (μ i))
    (hsum : Summable fun i ↦ π i * ∫ t, t ∂μ i) :
    Integrable (fun t : ℝ ↦ t) (probabilityMomentMixture π μ) ∧
      ∫ t, t ∂probabilityMomentMixture π μ = ∑' i, π i * ∫ t, t ∂μ i := by
  have hpositive := weighted_measure_moment μ π (fun i ↦ ∫ t, t ∂μ i)
    (fun t ↦ t) (∑' i, π i * ∫ t, t ∂μ i) hπ hint hnonneg (fun _ ↦ rfl) hsum.hasSum
  exact (atom_add_measure_moment _ _ (fun t : ℝ ↦ t) hpositive.1 rfl).imp
    id fun heq ↦ heq.trans hpositive.2

/-- The weights after length bias are nonnegative and have sum one. -/
theorem lengthBias_mixture_weights (π m : ℕ → ℝ)
    (hπ : ∀ i, 0 ≤ π i) (hm : ∀ i, 0 ≤ m i)
    (hsum : Summable fun i ↦ π i * m i) (hmean : 0 < ∑' i, π i * m i) :
    (∀ i, 0 ≤ π i * m i / ∑' j, π j * m j) ∧
      HasSum (fun i ↦ π i * m i / ∑' j, π j * m j) 1 := by
  refine ⟨fun i ↦ div_nonneg (mul_nonneg (hπ i) (hm i)) hmean.le, ?_⟩
  simpa only [div_self hmean.ne'] using hsum.hasSum.div_const (∑' i, π i * m i)

/-- Historical V1.6 Lemma 4.2: length bias of a countable mixture is the mixture of the biased laws,
with weights proportional to the original weights times the component means. -/
theorem lengthBias_probabilityMomentMixture (π : ℕ → ℝ) (μ : ℕ → Measure ℝ)
    (hπ : ∀ i, 0 ≤ π i) (hnonneg : ∀ i, ∀ᵐ t ∂μ i, 0 ≤ t)
    (hint : ∀ i, Integrable (fun t : ℝ ↦ t) (μ i))
    (hm : ∀ i, 0 < ∫ t, t ∂μ i)
    (hsum : Summable fun i ↦ π i * ∫ t, t ∂μ i)
    (hmean : 0 < ∑' i, π i * ∫ t, t ∂μ i) :
    lengthBias (probabilityMomentMixture π μ) =
      Measure.sum (fun i ↦
        ENNReal.ofReal ((π i * ∫ t, t ∂μ i) / (∑' j, π j * ∫ t, t ∂μ j)) •
          lengthBias (μ i)) := by
  let m : ℕ → ℝ := fun i ↦ ∫ t, t ∂μ i
  let s : ℝ := ∑' i, π i * m i
  have hactual : ∫ t, t ∂probabilityMomentMixture π μ = s :=
    (probabilityMomentMixture_first_moment π μ hπ hnonneg hint hsum).2
  rw [lengthBias, hactual, probabilityMomentMixture, withDensity_add_measure,
    withDensity_smul_measure, dirac_withDensity, zero_div, ENNReal.ofReal_zero,
    zero_smul, smul_zero, zero_add, withDensity_sum]
  congr 1
  funext i
  rw [withDensity_smul_measure, lengthBias,
    ← withDensity_smul _ (by fun_prop), ← withDensity_smul _ (by fun_prop)]
  congr 1
  funext t
  change ENNReal.ofReal (π i) * ENNReal.ofReal (t / s) =
    ENNReal.ofReal (π i * m i / s) * ENNReal.ofReal (t / m i)
  rw [← ENNReal.ofReal_mul (hπ i),
    ← ENNReal.ofReal_mul (div_nonneg (mul_nonneg (hπ i) (hm i).le) hmean.le)]
  congr 1
  change π i * (t / s) = (π i * m i / s) * (t / m i)
  field_simp [show m i ≠ 0 from (hm i).ne']

end SSPRK
