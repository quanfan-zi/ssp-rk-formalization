import SSPRK.PhaseTypeAllMoments

/-!
# Normalization of the transient initial mass

Normalizing a positive initial mass removes the immediate-absorption atom. The original
law is the mixture of that atom and the normalized phase-type law.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace SSPRK.PhaseTypeData

variable {s : ℕ} (d : PhaseTypeData s)

/-- Normalize the initial transient row to mass one while preserving the dynamics. -/
noncomputable def normalizeInitial (hm : 0 < d.mass) : PhaseTypeData s where
  transition := d.transition
  initial := d.mass⁻¹ • d.initial
  rate := d.rate
  rate_pos := d.rate_pos
  substochastic := d.substochastic
  transient := d.transient
  initial_nonneg := fun i ↦ mul_nonneg (inv_nonneg.mpr hm.le) (d.initial_nonneg i)
  initial_mass_le := by
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    change d.mass⁻¹ * d.mass ≤ 1
    rw [inv_mul_cancel₀ hm.ne']

@[simp]
theorem normalizeInitial_transition (hm : 0 < d.mass) :
    (d.normalizeInitial hm).transition = d.transition := rfl

@[simp]
theorem normalizeInitial_rate (hm : 0 < d.mass) : (d.normalizeInitial hm).rate = d.rate := rfl

@[simp]
theorem normalizeInitial_initial (hm : 0 < d.mass) :
    (d.normalizeInitial hm).initial = d.mass⁻¹ • d.initial := rfl

@[simp]
theorem normalizeInitial_mass (hm : 0 < d.mass) : (d.normalizeInitial hm).mass = 1 := by
  change (∑ i, d.mass⁻¹ * d.initial i) = 1
  rw [← Finset.mul_sum]
  exact inv_mul_cancel₀ hm.ne'

@[simp]
theorem normalizeInitial_green (hm : 0 < d.mass) : (d.normalizeInitial hm).green = d.green := rfl

@[simp]
theorem normalizeInitial_generator (hm : 0 < d.mass) :
    (d.normalizeInitial hm).generator = d.generator := rfl

@[simp]
theorem normalizeInitial_exit (hm : 0 < d.mass) : (d.normalizeInitial hm).exit = d.exit := rfl

/-- Every absorption-count weight is divided by the original transient mass. -/
theorem normalizeInitial_weight (hm : 0 < d.mass) (k : ℕ) :
    (d.normalizeInitial hm).weight k = d.weight k / d.mass := by
  simp only [weight, normalizeInitial_initial, normalizeInitial_transition,
    normalizeInitial_exit, smul_dotProduct, smul_eq_mul]
  ring

/-- Normalization divides every Green pairing by the initial mass. -/
theorem normalizeInitial_green_moment (hm : 0 < d.mass) (k : ℕ) :
    dotProduct (d.normalizeInitial hm).initial
      (((d.normalizeInitial hm).green ^ k).mulVec (fun _ ↦ (1 : ℝ))) =
        dotProduct d.initial ((d.green ^ k).mulVec (fun _ ↦ (1 : ℝ))) / d.mass := by
  simp only [normalizeInitial_initial, normalizeInitial_green, smul_dotProduct, smul_eq_mul]
  ring

/-- Normalization divides every positive integral moment by the initial mass. -/
theorem normalizeInitial_integral_pow (hm : 0 < d.mass) (k : ℕ) (hk : 0 < k) :
    ∫ x, x ^ k ∂(d.normalizeInitial hm).measure = (∫ x, x ^ k ∂d.measure) / d.mass := by
  rw [(d.normalizeInitial hm).integral_pow_measure k hk, d.integral_pow_measure k hk,
    d.normalizeInitial_green_moment hm, d.normalizeInitial_rate]
  ring

/-- The normalized law has no immediate-absorption atom. -/
theorem normalizeInitial_measure_eq_positiveMeasure (hm : 0 < d.mass) :
    (d.normalizeInitial hm).measure = (d.normalizeInitial hm).positiveMeasure := by
  rw [measure, d.normalizeInitial_mass hm]
  simp

/-- The positive-time measure is the original mass times the normalized positive-time measure. -/
theorem positiveMeasure_eq_smul_normalizeInitial (hm : 0 < d.mass) :
    d.positiveMeasure = ENNReal.ofReal d.mass • (d.normalizeInitial hm).positiveMeasure := by
  have hcoeff (k : ℕ) : ENNReal.ofReal d.mass *
      ENNReal.ofReal ((d.normalizeInitial hm).weight k) = ENNReal.ofReal (d.weight k) := by
    rw [← ENNReal.ofReal_mul hm.le, d.normalizeInitial_weight hm]
    congr 1
    field_simp
  ext t ht
  rw [positiveMeasure, Measure.sum_apply _ ht, Measure.smul_apply,
    positiveMeasure, Measure.sum_apply _ ht]
  simp only [Measure.smul_apply, smul_eq_mul, normalizeInitial_rate]
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro k
  rw [← mul_assoc, hcoeff]

/-- The initial row is its transient mass times the normalized initial row. -/
theorem mass_smul_normalizeInitial_initial (hm : 0 < d.mass) :
    d.mass • (d.normalizeInitial hm).initial = d.initial := by
  rw [normalizeInitial_initial, smul_smul, mul_inv_cancel₀ hm.ne', one_smul]

/-- The original law is the zero atom mixed with the normalized transient law. -/
theorem measure_eq_atom_add_normalizeInitial (hm : 0 < d.mass) :
    d.measure = ENNReal.ofReal (1 - d.mass) • Measure.dirac 0 +
      ENNReal.ofReal d.mass • (d.normalizeInitial hm).measure := by
  calc
    d.measure = ENNReal.ofReal (1 - d.mass) • Measure.dirac 0 + d.positiveMeasure := rfl
    _ = _ := by
      rw [d.positiveMeasure_eq_smul_normalizeInitial hm,
        d.normalizeInitial_measure_eq_positiveMeasure hm]

/-- The normalized law assigns zero mass to immediate absorption. -/
@[simp]
theorem normalizeInitial_measure_singleton_zero (hm : 0 < d.mass) :
    (d.normalizeInitial hm).measure {0} = 0 := by
  rw [(d.normalizeInitial hm).measure_apply_singleton_zero, d.normalizeInitial_mass hm]
  simp

end SSPRK.PhaseTypeData
