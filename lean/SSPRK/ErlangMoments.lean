import Mathlib.Probability.Distributions.Gamma
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! Integral moments of gamma distributions and their Erlang specializations. -/

open MeasureTheory Real Set Filter

namespace SSPRK

theorem ae_nonneg_gammaMeasure (a r : ℝ) :
    ∀ᵐ x ∂ProbabilityTheory.gammaMeasure a r, 0 ≤ x := by
  unfold ProbabilityTheory.gammaMeasure ProbabilityTheory.gammaPDF
  rw [ae_withDensity_iff (ProbabilityTheory.measurable_gammaPDFReal a r).ennreal_ofReal]
  apply ae_of_all
  intro x hx
  by_contra h
  exact hx (by simp [ProbabilityTheory.gammaPDFReal, h])

theorem integral_gammaMeasure_eq {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (f : ℝ → ℝ) :
    ∫ x, f x ∂ProbabilityTheory.gammaMeasure a r =
      ∫ x, ProbabilityTheory.gammaPDFReal a r x * f x := by
  unfold ProbabilityTheory.gammaMeasure ProbabilityTheory.gammaPDF
  rw [integral_withDensity_eq_integral_toReal_smul
      (ProbabilityTheory.measurable_gammaPDFReal a r).ennreal_ofReal
      (ae_of_all _ (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal
    (ProbabilityTheory.gammaPDFReal_nonneg ha hr _), smul_eq_mul]

theorem integral_pow_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (k : ℕ) :
    ∫ x, x ^ k ∂ProbabilityTheory.gammaMeasure a r =
      Gamma (a + k) / Gamma a / r ^ k := by
  rw [integral_gammaMeasure_eq ha hr]
  have hind : (fun x ↦ ProbabilityTheory.gammaPDFReal a r x * x ^ k) =
      (Ici 0).indicator
        (fun x ↦ (r ^ a / Gamma a) * (x ^ (a - 1) * exp (-(r * x)) * x ^ k)) := by
    funext x
    simp only [ProbabilityTheory.gammaPDFReal, indicator_apply, mem_Ici]
    split_ifs <;> ring
  rw [hind, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_const_mul]
  have hkernel : ∫ x : ℝ in Ioi 0, x ^ (a - 1) * exp (-(r * x)) * x ^ k =
      ∫ x : ℝ in Ioi 0, x ^ (a + k - 1) * exp (-(r * x)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [show a + (k : ℝ) - 1 = (a - 1) + k by ring, rpow_add hx,
      rpow_natCast]
    ring
  rw [hkernel, integral_rpow_mul_exp_neg_mul_Ioi (by positivity) hr,
    rpow_add (by positivity : 0 < 1 / r), rpow_natCast,
    div_rpow zero_le_one hr.le, one_rpow, one_div_pow]
  field_simp

theorem integrable_pow_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (k : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ k) (ProbabilityTheory.gammaMeasure a r) := by
  by_contra h
  have hz := integral_undef h
  rw [integral_pow_gammaMeasure ha hr] at hz
  exact (ne_of_gt (by positivity : 0 < Gamma (a + k) / Gamma a / r ^ k)) hz

theorem integral_id_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫ x, x ∂ProbabilityTheory.gammaMeasure a r = a / r := by
  simpa [Gamma_add_one ha.ne', (Gamma_pos_of_pos ha).ne'] using
    integral_pow_gammaMeasure ha hr 1

theorem integral_sq_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫ x, x ^ 2 ∂ProbabilityTheory.gammaMeasure a r = a * (a + 1) / r ^ 2 := by
  rw [integral_pow_gammaMeasure ha hr]
  norm_num only [Nat.cast_ofNat]
  rw [show a + 2 = (a + 1) + 1 by ring,
    Gamma_add_one (by positivity : a + 1 ≠ 0), Gamma_add_one ha.ne']
  field_simp

theorem integrable_id_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    Integrable (fun x : ℝ ↦ x) (ProbabilityTheory.gammaMeasure a r) := by
  simpa using integrable_pow_gammaMeasure ha hr 1

theorem integrable_sq_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    Integrable (fun x : ℝ ↦ x ^ 2) (ProbabilityTheory.gammaMeasure a r) :=
  integrable_pow_gammaMeasure ha hr 2

theorem integral_pow_erlangMeasure (n k : ℕ) {r : ℝ} (hr : 0 < r) :
    ∫ x, x ^ k ∂ProbabilityTheory.gammaMeasure (n + 1) r =
      ((n + k).factorial : ℝ) / n.factorial / r ^ k := by
  rw [integral_pow_gammaMeasure (by positivity) hr,
    show (n : ℝ) + 1 + k = (n + k : ℕ) + 1 by push_cast; ring,
    Gamma_nat_eq_factorial, Gamma_nat_eq_factorial]

theorem integral_id_erlangMeasure (n : ℕ) {r : ℝ} (hr : 0 < r) :
    ∫ x, x ∂ProbabilityTheory.gammaMeasure (n + 1) r = (n + 1) / r :=
  integral_id_gammaMeasure (by positivity) hr

theorem integral_sq_erlangMeasure (n : ℕ) {r : ℝ} (hr : 0 < r) :
    ∫ x, x ^ 2 ∂ProbabilityTheory.gammaMeasure (n + 1) r =
      (n + 1) * (n + 2) / r ^ 2 := by
  convert integral_sq_gammaMeasure (by positivity : 0 < (n : ℝ) + 1) hr using 1
  ring

end SSPRK
