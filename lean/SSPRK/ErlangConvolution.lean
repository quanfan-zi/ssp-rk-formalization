import SSPRK.ErlangLaplace
import SSPRK.LaplaceUniqueness
import SSPRK.MomentConvolution

/-!
# Independent exponential clocks

Convolution of gamma laws with a common rate adds their shapes. Iterating independent
exponential holding times therefore gives the Erlang laws used in uniformization.
-/

open MeasureTheory ProbabilityTheory

namespace SSPRK

/-- The Laplace integral of an independent sum factors into the two marginal integrals. -/
theorem integral_exp_neg_mul_independentSumLaw (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (u : ℝ) :
    (∫ x, Real.exp (-u * x) ∂independentSumLaw μ ν) =
      (∫ x, Real.exp (-u * x) ∂μ) * ∫ y, Real.exp (-u * y) ∂ν := by
  rw [independentSumLaw_integral μ ν _ (by fun_prop)]
  simp_rw [mul_add, Real.exp_add]
  exact integral_prod_mul (fun x : ℝ ↦ Real.exp (-u * x))
    (fun y : ℝ ↦ Real.exp (-u * y))

/-- Two independent gamma variables with a common rate have a gamma sum. -/
theorem independentSumLaw_gammaMeasure {a b r : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    independentSumLaw (gammaMeasure a r) (gammaMeasure b r) = gammaMeasure (a + b) r := by
  letI := isProbabilityMeasure_gammaMeasure ha hr
  letI := isProbabilityMeasure_gammaMeasure hb hr
  letI := isProbabilityMeasure_gammaMeasure (add_pos ha hb) hr
  apply Measure.ext_of_laplace_eq_of_ae_nonneg
    (independentSumLaw_ae_nonneg _ _ (ae_nonneg_gammaMeasure a r)
      (ae_nonneg_gammaMeasure b r)) (ae_nonneg_gammaMeasure (a + b) r)
  intro u hu
  rw [integral_exp_neg_mul_independentSumLaw,
    integral_exp_neg_mul_gammaMeasure ha hr hu,
    integral_exp_neg_mul_gammaMeasure hb hr hu,
    integral_exp_neg_mul_gammaMeasure (add_pos ha hb) hr hu]
  exact (Real.rpow_add (by positivity : 0 < r / (r + u)) a b).symm

/-- The law of the sum of `n` independent exponential clocks, defined by convolution. -/
noncomputable def exponentialClockSumLaw (r : ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => independentSumLaw (exponentialClockSumLaw r n) (gammaMeasure 1 r)

/-- A positive number of independent exponential clocks has the Erlang law. -/
theorem exponentialClockSumLaw_succ (n : ℕ) {r : ℝ} (hr : 0 < r) :
    exponentialClockSumLaw r (n + 1) = gammaMeasure (n + 1) r := by
  induction n with
  | zero =>
      letI := isProbabilityMeasure_gammaMeasure (show (0 : ℝ) < 1 by norm_num) hr
      simp [exponentialClockSumLaw, independentSumLaw]
  | succ n ih =>
      rw [exponentialClockSumLaw, ih,
        independentSumLaw_gammaMeasure (by positivity) (by norm_num) hr]
      simp only [Nat.cast_add, Nat.cast_one]

end SSPRK
