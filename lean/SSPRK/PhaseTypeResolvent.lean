import SSPRK.PhaseTypeGenerator
import SSPRK.ScaledResolvent

/-!
# Resolvent conversion for uniformized phase-type laws

The discrete generating-function resolvent is a scalar multiple of the continuous
generator resolvent. The exit vector scales by the same clock rate.
-/

namespace SSPRK.PhaseTypeData

variable {s : ℕ} (d : PhaseTypeData s)

/-- Factoring a shifted generator isolates the uniformization ratio. -/
theorem laplace_shift_eq (u : ℝ) (hu : 0 ≤ u) :
    u • (1 : Matrix (Fin s) (Fin s) ℝ) - d.generator =
      (d.rate + u) • (1 - (d.rate / (d.rate + u)) • d.transition) := by
  have hsum : 0 < d.rate + u := add_pos_of_pos_of_nonneg d.rate_pos hu
  have hcoeff : (d.rate + u) * (d.rate / (d.rate + u)) = d.rate := by
    field_simp
  simp only [generator, smul_sub, smul_smul, hcoeff, add_smul]
  abel

/-- The positive Laplace shift of a transient generator is nonsingular. -/
theorem laplace_shift_det_ne_zero (u : ℝ) (hu : 0 ≤ u) :
    (u • (1 : Matrix (Fin s) (Fin s) ℝ) - d.generator).det ≠ 0 := by
  rw [d.laplace_shift_eq u hu, Matrix.det_smul]
  apply mul_ne_zero (pow_ne_zero _ (ne_of_gt (add_pos_of_pos_of_nonneg d.rate_pos hu)))
  apply d.substochastic.one_sub_smul_det_ne_zero d.transient
  · exact div_nonneg d.rate_pos.le (add_nonneg d.rate_pos.le hu)
  · exact (div_le_one (add_pos_of_pos_of_nonneg d.rate_pos hu)).mpr (le_add_of_nonneg_right hu)

/-- Scalar conversion between the continuous and discrete resolvents. -/
theorem laplace_resolvent_eq (u : ℝ) (hu : 0 ≤ u) :
    (u • (1 : Matrix (Fin s) (Fin s) ℝ) - d.generator)⁻¹ =
      (d.rate + u)⁻¹ • (1 - (d.rate / (d.rate + u)) • d.transition)⁻¹ := by
  letI : Invertible (d.rate + u) :=
    invertibleOfNonzero (ne_of_gt (add_pos_of_pos_of_nonneg d.rate_pos hu))
  have hdet : (1 - (d.rate / (d.rate + u)) • d.transition).det ≠ 0 :=
    d.substochastic.one_sub_smul_det_ne_zero d.transient
      (div_nonneg d.rate_pos.le (add_nonneg d.rate_pos.le hu))
      ((div_le_one (add_pos_of_pos_of_nonneg d.rate_pos hu)).mpr
        (le_add_of_nonneg_right hu))
  rw [d.laplace_shift_eq u hu, Matrix.inv_smul _ _ (isUnit_iff_ne_zero.mpr hdet),
    invOf_eq_inv]

/-- Pairing the continuous resolvent with its exit vector cancels the clock scaling. -/
theorem laplace_resolvent_exit (u : ℝ) (hu : 0 ≤ u) :
    dotProduct d.initial
        ((u • (1 : Matrix (Fin s) (Fin s) ℝ) - d.generator)⁻¹.mulVec
          ((-d.generator).mulVec (fun _ ↦ 1))) =
      d.rate / (d.rate + u) *
        dotProduct d.initial
          (((1 - (d.rate / (d.rate + u)) • d.transition)⁻¹).mulVec d.exit) := by
  rw [d.laplace_resolvent_eq u hu, d.neg_generator]
  simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
    exit, div_eq_mul_inv, mul_assoc]

end SSPRK.PhaseTypeData
