import SSPRK.PhaseTypeNormalization
import SSPRK.PhaseTypeThirdLaw
import Mathlib.Probability.ConditionalProbability

/-!
# Conditioning a PH law on a positive absorption time

Normalizing the initial transient mass is exactly conditional probability on the
positive half-line. This relates the zero-atom decomposition to the language of
conditional laws on strictly positive times.
-/

open MeasureTheory ProbabilityTheory Set

namespace SSPRK.PhaseTypeData

/-- The normalized initial law is almost surely strictly positive. -/
theorem normalizeInitial_ae_pos {s : ℕ} (d : PhaseTypeData s) (hm : 0 < d.mass) :
    ∀ᵐ x ∂(d.normalizeInitial hm).measure, 0 < x := by
  have hz : (d.normalizeInitial hm).measure (Iic 0) = 0 := by
    rw [← Iio_union_right]
    exact measure_union_null (d.normalizeInitial hm).measure_apply_Iio_zero
      (d.normalizeInitial_measure_singleton_zero hm)
  rw [ae_iff]
  simpa only [not_lt] using hz

/-- Restricting to positive times removes the initial zero atom. -/
theorem restrict_positive_eq_smul_normalizeInitial {s : ℕ} (d : PhaseTypeData s)
    (hm : 0 < d.mass) :
    d.measure.restrict (Ioi 0) = ENNReal.ofReal d.mass • (d.normalizeInitial hm).measure := by
  rw [d.measure_eq_atom_add_normalizeInitial hm, Measure.restrict_add,
    Measure.restrict_smul, Measure.restrict_smul,
    Measure.restrict_eq_self_of_ae_mem (s := Ioi 0) (d.normalizeInitial_ae_pos hm)]
  have hzero : (Measure.dirac (0 : ℝ)).restrict (Ioi 0) = 0 := by simp
  rw [hzero, smul_zero, zero_add]

/-- The probability of a positive absorption time equals the initial transient mass. -/
theorem measure_positive_eq_mass {s : ℕ} (d : PhaseTypeData s) (hm : 0 < d.mass) :
    d.measure (Ioi 0) = ENNReal.ofReal d.mass := by
  have h := congrArg (fun μ : Measure ℝ ↦ μ univ) (d.restrict_positive_eq_smul_normalizeInitial hm)
  simpa only [Measure.restrict_apply_univ, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one] using h

/-- Conditioning on a positive absorption time normalizes the initial transient row. -/
theorem cond_positive_eq_normalizeInitial {s : ℕ} (d : PhaseTypeData s) (hm : 0 < d.mass) :
    ProbabilityTheory.cond d.measure (Ioi 0) = (d.normalizeInitial hm).measure := by
  rw [ProbabilityTheory.cond, d.measure_positive_eq_mass hm,
    d.restrict_positive_eq_smul_normalizeInitial hm,
    smul_smul, ENNReal.inv_mul_cancel (by exact ENNReal.ofReal_ne_zero_iff.mpr hm)
      ENNReal.ofReal_ne_top, one_smul]

/-- Removing a zero atom preserves equality in the third-moment ratio. -/
theorem third_integral_eq_normalize_iff {s : ℕ} (d : PhaseTypeData s) (hm : 0 < d.mass) :
    (((s : ℝ) + 2) * (∫ x, x ^ 2 ∂(d.normalizeInitial hm).measure) ^ 2 =
      ((s : ℝ) + 1) * (∫ x, x ∂(d.normalizeInitial hm).measure) *
        (∫ x, x ^ 3 ∂(d.normalizeInitial hm).measure)) ↔
    (((s : ℝ) + 2) * (∫ x, x ^ 2 ∂d.measure) ^ 2 =
      ((s : ℝ) + 1) * (∫ x, x ∂d.measure) * (∫ x, x ^ 3 ∂d.measure)) := by
  have hfirst := d.normalizeInitial_integral_pow hm 1 (by norm_num)
  simp only [pow_one] at hfirst
  rw [hfirst, d.normalizeInitial_integral_pow hm 2 (by norm_num),
    d.normalizeInitial_integral_pow hm 3 (by norm_num)]
  field_simp

/-- Third-moment equality characterized by the conditional law on strictly positive times. -/
theorem third_integral_eq_iff_cond_erlang {s : ℕ} (d : PhaseTypeData s) (hs : 0 < s)
    (hmean : 0 < ∫ x, x ∂d.measure) :
    (((s : ℝ) + 2) * (∫ x, x ^ 2 ∂d.measure) ^ 2 =
      ((s : ℝ) + 1) * (∫ x, x ∂d.measure) * (∫ x, x ^ 3 ∂d.measure)) ↔
    ∃ κ : ℝ, 0 < κ ∧ ProbabilityTheory.cond d.measure (Ioi 0) = gammaMeasure (s : ℝ) κ := by
  have hgreen : 0 < dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)) := by
    rw [d.integral_id_measure] at hmean
    exact (div_pos_iff_of_pos_right d.rate_pos).mp hmean
  have hm := d.mass_pos_of_green_mean_pos hgreen
  have hfirst := d.normalizeInitial_integral_pow hm 1 (by norm_num)
  simp only [pow_one] at hfirst
  have hnormmean : 0 < ∫ x, x ∂(d.normalizeInitial hm).measure := by
    rw [hfirst]
    exact div_pos hmean hm
  have hiff := (d.normalizeInitial hm).third_integral_eq_iff_atom_add_gamma hs hnormmean
  rw [d.third_integral_eq_normalize_iff hm] at hiff
  rw [d.cond_positive_eq_normalizeInitial hm]
  simpa only [d.normalizeInitial_mass hm, sub_self, ENNReal.ofReal_zero, zero_smul,
    zero_add, ENNReal.ofReal_one, one_smul] using hiff

end SSPRK.PhaseTypeData
