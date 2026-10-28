import SSPRK.ErlangMoments

/-! Positivity, recurrence, and adjacent ratios for all gamma moments. -/

open MeasureTheory ProbabilityTheory Real

namespace SSPRK

/-- All nonnegative integer moments of a gamma law are positive, including order zero. -/
theorem integral_pow_gammaMeasure_pos {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (k : ℕ) :
    0 < ∫ x, x ^ k ∂gammaMeasure a r := by
  rw [integral_pow_gammaMeasure ha hr]
  positivity

/-- Successive gamma moments satisfy the gamma-function recurrence. -/
theorem integral_pow_succ_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (k : ℕ) :
    (∫ x, x ^ (k + 1) ∂gammaMeasure a r) =
      (a + k) / r * (∫ x, x ^ k ∂gammaMeasure a r) := by
  rw [integral_pow_gammaMeasure ha hr, integral_pow_gammaMeasure ha hr]
  rw [Nat.cast_add, Nat.cast_one, ← add_assoc,
    Gamma_add_one (by positivity : a + (k : ℝ) ≠ 0), pow_succ]
  ring

/-- The adjacent gamma moment ratio at every nonnegative integer order. -/
theorem gamma_adjacent_moment_ratio {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (k : ℕ) :
    (∫ x, x ^ k ∂gammaMeasure a r) * (∫ x, x ^ (k + 2) ∂gammaMeasure a r) /
        (∫ x, x ^ (k + 1) ∂gammaMeasure a r) ^ 2 =
      (a + k + 1) / (a + k) := by
  have hm := ne_of_gt (integral_pow_gammaMeasure_pos ha hr k)
  have hak : a + (k : ℝ) ≠ 0 := by positivity
  rw [show k + 2 = (k + 1) + 1 by omega,
    integral_pow_succ_gammaMeasure ha hr (k + 1),
    integral_pow_succ_gammaMeasure ha hr k]
  push_cast
  field_simp
  ring

end SSPRK
