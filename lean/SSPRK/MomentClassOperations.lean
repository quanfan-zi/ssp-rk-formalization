import SSPRK.MomentAlgebra

/-!
# Scaling and enlargement of moment classes

Positive time scaling preserves the two moment inequalities. Increasing the state-count
parameter weakens them. The normalized auxiliary triple used in state elimination belongs
to the one-state class whenever its two correction terms are nonnegative.
-/

namespace SSPRK

/-- A positive mean and the second-moment bound force a positive second moment. -/
theorem MomentClass.second_pos {k x a c : ℝ} (hx : MomentClass k x a c) : 0 < a := by
  have hprod : 0 < k * a := lt_of_lt_of_le
    (mul_pos (by linarith [hx.parameter_pos]) (sq_pos_of_pos hx.mean_pos)) hx.second_bound
  exact (mul_pos_iff_of_pos_left hx.parameter_pos).mp hprod

/-- Positive scaling of a random time scales its first three moments homogeneously. -/
theorem MomentClass.scale {k x a c t : ℝ} (hx : MomentClass k x a c) (ht : 0 < t) :
    MomentClass k (t * x) (t ^ 2 * a) (t ^ 3 * c) := by
  refine ⟨hx.parameter_pos, mul_pos ht hx.mean_pos, ?_, ?_, ?_, ?_⟩
  · exact mul_nonneg (sq_nonneg t) hx.second_nonneg
  · exact mul_nonneg (pow_nonneg ht.le _) hx.third_nonneg
  · nlinarith only [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hx.second_bound)]
  · nlinarith only [mul_nonneg (pow_nonneg ht.le 4) (sub_nonneg.mpr hx.third_bound)]

/-- Increasing the allowed state count weakens both moment bounds. -/
theorem MomentClass.mono_parameter {k l x a c : ℝ} (hx : MomentClass k x a c)
    (hkl : k ≤ l) : MomentClass l x a c := by
  have hs : x ^ 2 ≤ a := by
    apply sub_nonneg.mp
    apply nonneg_of_mul_nonneg_left (b := k) _ hx.parameter_pos
    nlinarith only [hx.second_bound, sq_nonneg x]
  have ht : a ^ 2 ≤ x * c := by
    apply sub_nonneg.mp
    apply nonneg_of_mul_nonneg_left (b := k + 1) _ (by linarith [hx.parameter_pos])
    nlinarith only [hx.third_bound, sq_nonneg a]
  refine ⟨lt_of_lt_of_le hx.parameter_pos hkl, hx.mean_pos,
    hx.second_nonneg, hx.third_nonneg, ?_, ?_⟩
  · nlinarith only [hx.second_bound,
      mul_nonneg (sub_nonneg.mpr hkl) (sub_nonneg.mpr hs)]
  · nlinarith only [hx.third_bound,
      mul_nonneg (sub_nonneg.mpr hkl) (sub_nonneg.mpr ht)]

/-- The normalized correction triple in state elimination satisfies the one-state bounds. -/
theorem auxiliary_moment_class {η1 η2 : ℝ} (hη1 : 0 ≤ η1) (hη2 : 0 ≤ η2) :
    MomentClass 1 1 (2 * (1 + η1)) (6 * (1 + η1) ^ 2 + 3 * η2) := by
  refine ⟨by norm_num, by norm_num, by positivity, by positivity, ?_, ?_⟩
  · nlinarith only [hη1]
  · nlinarith only [hη2]

end SSPRK
