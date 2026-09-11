import SSPRK.PhaseTypeVariance
import SSPRK.PhaseTypeThirdMomentIntegral

/-!
# Moment bounds for representations with at most a given number of states

The sharp bounds proved at the actual dimension imply the manuscript statements
for any larger allowed phase count.
-/

open MeasureTheory ProbabilityTheory

namespace SSPRK.PhaseTypeData

/-- The minimum-variance bound for a PH representation with at most `s` states. -/
theorem variance_lower_bound_of_le {m s : ℕ} (d : PhaseTypeData m)
    (hm : 0 < m) (hms : m ≤ s) :
    (∫ x, x ∂d.measure) ^ 2 / (s : ℝ) ≤ variance (fun x : ℝ ↦ x) d.measure := by
  exact le_trans (div_le_div_of_nonneg_left (sq_nonneg _)
    (Nat.cast_pos.mpr hm) (Nat.cast_le.mpr hms)) (d.variance_lower_bound hm)

/-- The two moment inequalities hold at every allowed state count above the actual dimension. -/
theorem integral_moment_class_of_le {m s : ℕ} (d : PhaseTypeData m) (hms : m ≤ s)
    (hmean : 0 < ∫ x, x ∂d.measure) :
    MomentClass s (∫ x, x ∂d.measure) (∫ x, x ^ 2 ∂d.measure) (∫ x, x ^ 3 ∂d.measure) :=
  (d.integral_moment_class hmean).mono_parameter (Nat.cast_le.mpr hms)

/-- The third-moment bound for any representation with at most `s` transient states. -/
theorem third_moment_lower_bound_of_le {m s : ℕ} (d : PhaseTypeData m) (hms : m ≤ s)
    (hmean : 0 < ∫ x, x ∂d.measure) :
    ((s : ℝ) + 2) * (∫ x, x ^ 2 ∂d.measure) ^ 2 ≤
      ((s : ℝ) + 1) * (∫ x, x ∂d.measure) * (∫ x, x ^ 3 ∂d.measure) :=
  (d.integral_moment_class_of_le hms hmean).third_bound

end SSPRK.PhaseTypeData
