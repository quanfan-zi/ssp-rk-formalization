import SSPRK.ErlangMoments
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Scaled exponential probability laws

The law below is the pushforward of the unit-rate exponential distribution by scalar
multiplication. The scale may be zero or negative; nonnegative scales retain nonnegative support.
-/

open MeasureTheory Set

namespace SSPRK

/-- The unit-rate exponential law scaled by the real factor `r`. -/
noncomputable def scaledExponentialLaw (r : ℝ) : Measure ℝ :=
  (ProbabilityTheory.gammaMeasure 1 1).map (fun x ↦ r * x)

instance scaledExponentialLaw_isProbabilityMeasure (r : ℝ) :
    IsProbabilityMeasure (scaledExponentialLaw r) := by
  have : IsProbabilityMeasure (ProbabilityTheory.gammaMeasure 1 1) :=
    ProbabilityTheory.isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- A nonnegative scaling of the exponential law is almost surely nonnegative. -/
theorem ae_nonneg_scaledExponentialLaw {r : ℝ} (hr : 0 ≤ r) :
    ∀ᵐ x ∂scaledExponentialLaw r, 0 ≤ x := by
  rw [scaledExponentialLaw]
  apply (MeasureTheory.ae_map_iff (by fun_prop) measurableSet_Ici).2
  exact (ae_nonneg_gammaMeasure 1 1).mono fun x hx ↦ mul_nonneg hr hx

/-- Every natural power is integrable under a scaled exponential law. -/
theorem integrable_pow_scaledExponentialLaw (r : ℝ) (k : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ k) (scaledExponentialLaw r) := by
  rw [scaledExponentialLaw,
    MeasureTheory.integrable_map_measure (by fun_prop) (by fun_prop)]
  change Integrable (fun x : ℝ ↦ (r * x) ^ k) (ProbabilityTheory.gammaMeasure 1 1)
  simpa only [mul_pow] using
    (integrable_pow_gammaMeasure (a := 1) (r := 1) (by norm_num) (by norm_num) k).const_mul
      (r ^ k)

/-- The `k`-th moment is `k! r^k`, for every real scale `r`. -/
theorem integral_pow_scaledExponentialLaw (r : ℝ) (k : ℕ) :
    ∫ x, x ^ k ∂scaledExponentialLaw r = (k.factorial : ℝ) * r ^ k := by
  rw [scaledExponentialLaw, MeasureTheory.integral_map (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow]
  rw [integral_const_mul]
  have hmom := integral_pow_erlangMeasure 0 k (r := 1) (by norm_num)
  norm_num at hmom
  rw [hmom]
  ring

end SSPRK
