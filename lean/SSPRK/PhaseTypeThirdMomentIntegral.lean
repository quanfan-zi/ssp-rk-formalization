import SSPRK.PhaseTypeAllMoments
import SSPRK.MomentClassOperations
import SSPRK.PhaseTypeThirdMoment

/-!
# Integral form of the PH third-moment inequality

The algebraic Green moments and the actual probability integrals differ by positive
time scaling. This module carries the state-count moment bounds to the probability law.
-/

open MeasureTheory

namespace SSPRK.PhaseTypeData

/-- Transfer both Green moment inequalities to the actual probability integrals. -/
theorem integral_momentClass_of_green {s : ℕ} (d : PhaseTypeData s)
    (hclass : MomentClass s (dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)))
      (2 * dotProduct d.initial ((d.green ^ 2).mulVec (fun _ ↦ 1)))
      (6 * dotProduct d.initial ((d.green ^ 3).mulVec (fun _ ↦ 1)))) :
    MomentClass s (∫ x, x ∂d.measure) (∫ x, x ^ 2 ∂d.measure) (∫ x, x ^ 3 ∂d.measure) := by
  convert hclass.scale (inv_pos.mpr d.rate_pos) using 1
  · rw [d.integral_id_measure]
    ring
  · rw [d.integral_pow_measure 2 (by norm_num)]
    norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_ofNat]
    simp only [div_eq_mul_inv, inv_pow]
    ring
  · rw [d.integral_pow_measure 3 (by norm_num)]
    norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_ofNat]
    simp only [div_eq_mul_inv, inv_pow]
    ring

/-- The first three actual moments of a nonzero PH time belong to the state-count class. -/
theorem integral_moment_class {s : ℕ} (d : PhaseTypeData s)
    (hmean : 0 < ∫ x, x ∂d.measure) :
    MomentClass s (∫ x, x ∂d.measure) (∫ x, x ^ 2 ∂d.measure) (∫ x, x ^ 3 ∂d.measure) := by
  apply d.integral_momentClass_of_green
  apply green_moment_class s d
  rw [d.integral_id_measure] at hmean
  exact (div_pos_iff_of_pos_right d.rate_pos).mp hmean

/-- The third-moment bound for actual PH integral moments, allowing zero atoms. -/
theorem third_moment_lower_bound {s : ℕ} (d : PhaseTypeData s)
    (hmean : 0 < ∫ x, x ∂d.measure) :
    ((s : ℝ) + 2) * (∫ x, x ^ 2 ∂d.measure) ^ 2 ≤
      ((s : ℝ) + 1) * (∫ x, x ∂d.measure) * (∫ x, x ^ 3 ∂d.measure) :=
  (d.integral_moment_class hmean).third_bound

/-- The adjacent third-moment ratio bound. -/
theorem third_moment_ratio_lower_bound {s : ℕ} (d : PhaseTypeData s)
    (hmean : 0 < ∫ x, x ∂d.measure) :
    ((s : ℝ) + 2) / ((s : ℝ) + 1) ≤
      (∫ x, x ∂d.measure) * (∫ x, x ^ 3 ∂d.measure) / (∫ x, x ^ 2 ∂d.measure) ^ 2 := by
  have hc := d.integral_moment_class hmean
  apply (div_le_div_iff₀ (by positivity : 0 < (s : ℝ) + 1)
    (sq_pos_of_pos hc.second_pos)).mpr
  nlinarith only [hc.third_bound]

end SSPRK.PhaseTypeData
