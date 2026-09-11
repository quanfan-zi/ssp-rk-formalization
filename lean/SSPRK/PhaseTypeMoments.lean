import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import SSPRK.PhaseType
import SSPRK.ErlangMoments
import SSPRK.PhaseTypeCountMoments

/-!
# Integral moments of finite phase-type laws

Countable nonnegative mixtures commute with integration once their component moments
are summable. This connects the Erlang mixture construction to Green-matrix moments.
-/

open MeasureTheory
open scoped ENNReal

namespace SSPRK

/-- Integrability and the moment of a countable weighted mixture of measures. -/
lemma weighted_measure_moment (μ : ℕ → Measure ℝ) (w a : ℕ → ℝ) (f : ℝ → ℝ)
    (m : ℝ) (hw : ∀ n, 0 ≤ w n) (hf : ∀ n, Integrable f (μ n))
    (hnonneg : ∀ n, ∀ᵐ x ∂μ n, 0 ≤ f x)
    (hmoment : ∀ n, ∫ x, f x ∂μ n = a n)
    (hsum : HasSum (fun n ↦ w n * a n) m) :
    Integrable f (Measure.sum (fun n ↦ ENNReal.ofReal (w n) • μ n)) ∧
      ∫ x, f x ∂Measure.sum (fun n ↦ ENNReal.ofReal (w n) • μ n) = m := by
  have hnorm (n : ℕ) : ∫ x, ‖f x‖ ∂μ n = a n := by
    rw [← hmoment n]
    exact integral_congr_ae ((hnonneg n).mono fun x hx ↦ Real.norm_of_nonneg hx)
  have hint : Integrable f (Measure.sum (fun n ↦ ENNReal.ofReal (w n) • μ n)) := by
    apply integrable_sum_measure (fun n ↦ (hf n).smul_measure ENNReal.ofReal_ne_top)
    simpa only [integral_smul_measure, ENNReal.toReal_ofReal (hw _), smul_eq_mul, hnorm]
      using hsum.summable
  refine ⟨hint, ?_⟩
  rw [integral_sum_measure hint]
  simpa only [integral_smul_measure, ENNReal.toReal_ofReal (hw _), smul_eq_mul, hmoment]
    using hsum.tsum_eq

/-- Adding an atom at a zero of the integrand preserves integrability and its integral. -/
lemma atom_add_measure_moment (μ : Measure ℝ) (c : ℝ) (f : ℝ → ℝ)
    (hf : Integrable f μ) (hzero : f 0 = 0) :
    Integrable f (ENNReal.ofReal c • Measure.dirac 0 + μ) ∧
      ∫ x, f x ∂(ENNReal.ofReal c • Measure.dirac 0 + μ) = ∫ x, f x ∂μ := by
  have hatom : Integrable f (ENNReal.ofReal c • Measure.dirac 0) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  refine ⟨hatom.add_measure hf, ?_⟩
  rw [integral_add_measure hatom hf, integral_smul_measure, integral_dirac, hzero]
  simp

namespace PhaseTypeData

variable {s : ℕ} (d : PhaseTypeData s)

/-- The first moment of the positive-time mixture, given its counting moment. -/
lemma positiveMeasure_first_moment_of_hasSum (m : ℝ)
    (hsum : HasSum (fun n : ℕ ↦ (n + 1 : ℝ) * d.weight n) m) :
    Integrable (fun x : ℝ ↦ x) d.positiveMeasure ∧
      ∫ x, x ∂d.positiveMeasure = m / d.rate := by
  apply weighted_measure_moment
    (fun n ↦ ProbabilityTheory.gammaMeasure (n + 1) d.rate)
    d.weight (fun n ↦ (n + 1) / d.rate) (fun x ↦ x) (m / d.rate) d.weight_nonneg
  · intro n
    exact integrable_id_gammaMeasure (by positivity) d.rate_pos
  · intro n
    exact ae_nonneg_gammaMeasure (n + 1) d.rate
  · intro n
    exact integral_id_erlangMeasure n d.rate_pos
  · convert hsum.div_const d.rate using 1
    ext n
    ring

/-- The second moment of the positive-time mixture, given its counting moment. -/
lemma positiveMeasure_second_moment_of_hasSum (m : ℝ)
    (hsum : HasSum (fun n : ℕ ↦ (n + 1 : ℝ) * (n + 2) * d.weight n) m) :
    Integrable (fun x : ℝ ↦ x ^ 2) d.positiveMeasure ∧
      ∫ x, x ^ 2 ∂d.positiveMeasure = m / d.rate ^ 2 := by
  apply weighted_measure_moment
    (fun n ↦ ProbabilityTheory.gammaMeasure (n + 1) d.rate)
    d.weight (fun n ↦ (n + 1) * (n + 2) / d.rate ^ 2) (fun x ↦ x ^ 2)
    (m / d.rate ^ 2) d.weight_nonneg
  · intro n
    exact integrable_sq_gammaMeasure (by positivity) d.rate_pos
  · intro n
    exact ae_of_all _ (fun x ↦ sq_nonneg x)
  · intro n
    exact integral_sq_erlangMeasure n d.rate_pos
  · convert hsum.div_const (d.rate ^ 2) using 1
    ext n
    ring

/-- The mean absorption time is the initial Green-matrix row sum divided by the clock rate. -/
theorem first_integral_moment :
    Integrable (fun x : ℝ ↦ x) d.measure ∧
      ∫ x, x ∂d.measure = dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)) / d.rate := by
  obtain ⟨hint, hmoment⟩ :=
    d.positiveMeasure_first_moment_of_hasSum _ d.hasSum_first_count_moment
  obtain ⟨hint', heq⟩ := atom_add_measure_moment d.positiveMeasure (1 - d.mass)
    (fun x ↦ x) hint rfl
  exact ⟨hint', heq.trans hmoment⟩

/-- The second absorption-time moment is twice the iterated Green moment over rate squared. -/
theorem second_integral_moment :
    Integrable (fun x : ℝ ↦ x ^ 2) d.measure ∧
      ∫ x, x ^ 2 ∂d.measure =
        2 * dotProduct d.initial (d.green.mulVec (d.green.mulVec (fun _ ↦ 1))) /
          d.rate ^ 2 := by
  obtain ⟨hint, hmoment⟩ :=
    d.positiveMeasure_second_moment_of_hasSum _ d.hasSum_second_count_moment
  obtain ⟨hint', heq⟩ := atom_add_measure_moment d.positiveMeasure (1 - d.mass)
    (fun x ↦ x ^ 2) hint (by norm_num)
  refine ⟨hint', ?_⟩
  simpa only [pow_two, Matrix.mulVec_mulVec] using heq.trans hmoment

/-- Absorption time is integrable under the phase-type law. -/
theorem integrable_id_measure : Integrable (fun x : ℝ ↦ x) d.measure :=
  d.first_integral_moment.1

/-- Green-matrix formula for the mean absorption time. -/
theorem integral_id_measure :
    ∫ x, x ∂d.measure = dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)) / d.rate :=
  d.first_integral_moment.2

/-- Squared absorption time is integrable under the phase-type law. -/
theorem integrable_sq_measure : Integrable (fun x : ℝ ↦ x ^ 2) d.measure :=
  d.second_integral_moment.1

/-- Green-matrix formula for the second absorption-time moment. -/
theorem integral_sq_measure :
    ∫ x, x ^ 2 ∂d.measure =
      2 * dotProduct d.initial (d.green.mulVec (d.green.mulVec (fun _ ↦ 1))) / d.rate ^ 2 :=
  d.second_integral_moment.2

end PhaseTypeData
end SSPRK
