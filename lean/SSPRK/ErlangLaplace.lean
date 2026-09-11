import SSPRK.ErlangMoments

/-! Laplace integrals of gamma distributions and their Erlang specializations. -/

open MeasureTheory Real Set Filter

namespace SSPRK

theorem integral_exp_neg_mul_gammaMeasure {a r u : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hu : 0 ≤ u) :
    ∫ x, exp (-u * x) ∂ProbabilityTheory.gammaMeasure a r = (r / (r + u)) ^ a := by
  rw [integral_gammaMeasure_eq ha hr]
  have hind : (fun x ↦ ProbabilityTheory.gammaPDFReal a r x * exp (-u * x)) =
      (Ici 0).indicator
        (fun x ↦ (r ^ a / Gamma a) * (x ^ (a - 1) * exp (-((r + u) * x)))) := by
    funext x
    simp only [ProbabilityTheory.gammaPDFReal, indicator_apply, mem_Ici]
    split_ifs
    · rw [show -((r + u) * x) = -(r * x) + -u * x by ring, exp_add]
      ring
    · ring
  rw [hind, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_const_mul, integral_rpow_mul_exp_neg_mul_Ioi ha (by positivity),
    div_rpow zero_le_one (by positivity : 0 ≤ r + u), one_rpow,
    div_rpow hr.le (by positivity : 0 ≤ r + u)]
  field_simp

theorem integrable_exp_neg_mul_gammaMeasure {a r u : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hu : 0 ≤ u) :
    Integrable (fun x : ℝ ↦ exp (-u * x)) (ProbabilityTheory.gammaMeasure a r) := by
  by_contra h
  have hz := integral_undef h
  rw [integral_exp_neg_mul_gammaMeasure ha hr hu] at hz
  exact (ne_of_gt (by positivity : 0 < (r / (r + u)) ^ a)) hz

theorem integral_exp_neg_mul_erlangMeasure (n : ℕ) {r u : ℝ}
    (hr : 0 < r) (hu : 0 ≤ u) :
    ∫ x, exp (-u * x) ∂ProbabilityTheory.gammaMeasure (n + 1) r =
      (r / (r + u)) ^ (n + 1) := by
  simpa only [← Nat.cast_add_one, rpow_natCast] using
    integral_exp_neg_mul_gammaMeasure (by positivity : 0 < (n : ℝ) + 1) hr hu

theorem integrable_exp_neg_mul_erlangMeasure (n : ℕ) {r u : ℝ}
    (hr : 0 < r) (hu : 0 ≤ u) :
    Integrable (fun x : ℝ ↦ exp (-u * x)) (ProbabilityTheory.gammaMeasure (n + 1) r) :=
  integrable_exp_neg_mul_gammaMeasure (by positivity) hr hu

end SSPRK
