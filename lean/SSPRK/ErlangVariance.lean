import SSPRK.ErlangMoments
import Mathlib.Probability.Moments.Variance

/-! # Variance and sharpness of the equal-rate Erlang law -/

open MeasureTheory ProbabilityTheory

namespace SSPRK

/-- The gamma shape and rate determine its variance. -/
theorem variance_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    variance (fun x : ℝ ↦ x) (gammaMeasure a r) = a / r ^ 2 := by
  letI : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasure_gammaMeasure ha hr
  rw [variance_eq_sub ((memLp_two_iff_integrable_sq (by fun_prop)).mpr
    (integrable_sq_gammaMeasure ha hr))]
  simp only [Pi.pow_apply, integral_sq_gammaMeasure ha hr, integral_id_gammaMeasure ha hr]
  ring

/-- An equal-rate Erlang law attains the phase-count variance bound. -/
theorem variance_erlang_eq_mean_sq_div {s : ℕ} (hs : 0 < s) {r : ℝ} (hr : 0 < r) :
    variance (fun x : ℝ ↦ x) (gammaMeasure (s : ℝ) r) =
      (∫ x, x ∂gammaMeasure (s : ℝ) r) ^ 2 / (s : ℝ) := by
  rw [variance_gammaMeasure (Nat.cast_pos.mpr hs) hr,
    integral_id_gammaMeasure (Nat.cast_pos.mpr hs) hr]
  field_simp

end SSPRK
