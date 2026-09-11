import SSPRK.PhaseTypeWeights
import Mathlib.Probability.Distributions.Gamma

/-!
# Probability measures from finite phase-type representations

A phase-type law is a countable mixture of Erlang laws. The missing initial mass is
placed at zero, while `weight n` multiplies the Erlang law with shape `n + 1`.
-/

open scoped ENNReal

open MeasureTheory Set

namespace SSPRK.PhaseTypeData

variable {s : ℕ} (d : PhaseTypeData s)

/-- The part of the phase-type law corresponding to positive absorption times. -/
noncomputable def positiveMeasure : Measure ℝ :=
  Measure.sum fun n : ℕ ↦
    ENNReal.ofReal (d.weight n) • ProbabilityTheory.gammaMeasure (n + 1) d.rate

/-- The probability law associated with a uniformized finite phase-type representation. -/
noncomputable def measure : Measure ℝ :=
  ENNReal.ofReal (1 - d.mass) • Measure.dirac 0 + d.positiveMeasure

/-- A weighted atom plus a countable mixture of probability measures is a probability
measure when its coefficients sum to one. -/
theorem isProbabilityMeasure_atom_add_sum {α ι : Type*} [MeasurableSpace α]
    (x : α) (c₀ : ℝ≥0∞) (c : ι → ℝ≥0∞) (μ : ι → Measure α)
    (hμ : ∀ i, IsProbabilityMeasure (μ i)) (hc : c₀ + ∑' i, c i = 1) :
    IsProbabilityMeasure
      (c₀ • Measure.dirac x + Measure.sum (fun i ↦ c i • μ i)) where
  measure_univ := by
    rw [Measure.add_apply, Measure.smul_apply, Measure.sum_apply _ MeasurableSet.univ]
    simp only [Measure.dirac_apply_of_mem (mem_univ x), smul_eq_mul, mul_one]
    simp_rw [Measure.smul_apply, smul_eq_mul, (hμ _).measure_univ, mul_one]
    exact hc

private theorem mass_nonneg : 0 ≤ d.mass := by
  exact Finset.sum_nonneg fun i _ ↦ d.initial_nonneg i

private theorem coefficient_tsum :
    ENNReal.ofReal (1 - d.mass) + ∑' n, ENNReal.ofReal (d.weight n) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg d.weight_nonneg d.summable_weight, d.tsum_weight]
  have hm : d.mass ≤ 1 := by simpa [mass] using d.initial_mass_le
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hm) d.mass_nonneg]
  simp

/-- The phase-type measure has total mass one. -/
theorem isProbabilityMeasure_measure : IsProbabilityMeasure d.measure := by
  apply isProbabilityMeasure_atom_add_sum
  · intro n
    exact ProbabilityTheory.isProbabilityMeasure_gammaMeasure (by positivity) d.rate_pos
  · exact d.coefficient_tsum

instance : IsProbabilityMeasure d.measure := d.isProbabilityMeasure_measure

private theorem gammaMeasure_Iio_zero (n : ℕ) :
    ProbabilityTheory.gammaMeasure (n + 1) d.rate (Iio 0) = 0 := by
  rw [ProbabilityTheory.gammaMeasure, withDensity_apply _ measurableSet_Iio]
  exact ProbabilityTheory.lintegral_gammaPDF_of_nonpos le_rfl

private theorem gammaMeasure_Iic_zero (n : ℕ) :
    ProbabilityTheory.gammaMeasure (n + 1) d.rate (Iic 0) = 0 := by
  rw [ProbabilityTheory.gammaMeasure, withDensity_apply _ measurableSet_Iic]
  rw [← Iio_union_right]
  rw [lintegral_union (measurableSet_singleton 0) (by simp)]
  rw [ProbabilityTheory.lintegral_gammaPDF_of_nonpos le_rfl]
  simp

private theorem gammaMeasure_singleton_zero (n : ℕ) :
    ProbabilityTheory.gammaMeasure (n + 1) d.rate {0} = 0 := by
  rw [ProbabilityTheory.gammaMeasure, withDensity_apply _ (measurableSet_singleton 0)]
  simp

/-- The positive-time mixture assigns no mass to negative values. -/
@[simp]
theorem positiveMeasure_apply_Iio_zero : d.positiveMeasure (Iio 0) = 0 := by
  rw [positiveMeasure, Measure.sum_apply _ measurableSet_Iio]
  simp [Measure.smul_apply, d.gammaMeasure_Iio_zero]

/-- The positive-time mixture assigns no mass to nonpositive values. -/
@[simp]
theorem positiveMeasure_apply_Iic_zero : d.positiveMeasure (Iic 0) = 0 := by
  rw [positiveMeasure, Measure.sum_apply _ measurableSet_Iic]
  simp [Measure.smul_apply, d.gammaMeasure_Iic_zero]

/-- The positive-time mixture has no atom at zero. -/
@[simp]
theorem positiveMeasure_apply_singleton_zero : d.positiveMeasure {0} = 0 := by
  rw [positiveMeasure, Measure.sum_apply _ (measurableSet_singleton 0)]
  simp [Measure.smul_apply, d.gammaMeasure_singleton_zero]

/-- The phase-type law is supported on the nonnegative half-line. -/
@[simp]
theorem measure_apply_Iio_zero : d.measure (Iio 0) = 0 := by
  simp [measure]

/-- The phase-type law gives full mass to the nonnegative half-line. -/
@[simp]
theorem measure_apply_Ici_zero : d.measure (Ici 0) = 1 := by
  rw [← prob_compl_eq_zero_iff measurableSet_Ici, compl_Ici]
  exact d.measure_apply_Iio_zero

/-- A phase-type random variable is almost surely nonnegative. -/
theorem ae_nonneg_measure : ∀ᵐ x ∂d.measure, 0 ≤ x := by
  rw [ae_iff]
  simpa only [not_le] using d.measure_apply_Iio_zero

/-- The mass on the nonpositive half-line is exactly the immediate-absorption mass. -/
@[simp]
theorem measure_apply_Iic_zero : d.measure (Iic 0) = ENNReal.ofReal (1 - d.mass) := by
  simp [measure]

/-- The only atom at zero is the immediate-absorption mass. -/
@[simp]
theorem measure_apply_singleton_zero : d.measure {0} = ENNReal.ofReal (1 - d.mass) := by
  simp [measure]

end SSPRK.PhaseTypeData
