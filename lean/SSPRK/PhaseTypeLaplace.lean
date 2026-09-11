import SSPRK.PhaseTypeMoments
import SSPRK.ErlangLaplace
import SSPRK.PhaseTypeGeneratingFunction

/-!
# Laplace transform of a finite phase-type law

The Erlang mixture turns the Laplace transform into the generating function of the
absorption weights. A separate algebraic identity evaluates that generating function
as a resolvent of the transient transition matrix.
-/

open MeasureTheory

namespace SSPRK.PhaseTypeData

variable {s : ℕ} (d : PhaseTypeData s)

/-- The Laplace transform of the positive-time mixture, assuming the corresponding
absorption-weight generating series. -/
lemma positiveMeasure_laplace_of_hasSum (u m : ℝ) (hu : 0 ≤ u)
    (hsum : HasSum
      (fun n : ℕ ↦ d.weight n * (d.rate / (d.rate + u)) ^ (n + 1)) m) :
    Integrable (fun x : ℝ ↦ Real.exp (-u * x)) d.positiveMeasure ∧
      ∫ x, Real.exp (-u * x) ∂d.positiveMeasure = m := by
  apply weighted_measure_moment
    (fun n ↦ ProbabilityTheory.gammaMeasure (n + 1) d.rate)
    d.weight (fun n ↦ (d.rate / (d.rate + u)) ^ (n + 1))
    (fun x ↦ Real.exp (-u * x)) m d.weight_nonneg
  · intro n
    exact integrable_exp_neg_mul_gammaMeasure (by positivity) d.rate_pos hu
  · intro n
    exact ae_of_all _ fun x ↦ (Real.exp_pos _).le
  · intro n
    exact integral_exp_neg_mul_erlangMeasure n d.rate_pos hu
  · exact hsum

/-- Adding the immediate-absorption atom contributes `1 - mass` to the Laplace
transform. -/
lemma measure_laplace_of_hasSum (u m : ℝ) (hu : 0 ≤ u)
    (hsum : HasSum
      (fun n : ℕ ↦ d.weight n * (d.rate / (d.rate + u)) ^ (n + 1)) m) :
    Integrable (fun x : ℝ ↦ Real.exp (-u * x)) d.measure ∧
      ∫ x, Real.exp (-u * x) ∂d.measure = 1 - d.mass + m := by
  obtain ⟨hint, hmoment⟩ := d.positiveMeasure_laplace_of_hasSum u m hu hsum
  have hatom : Integrable (fun x : ℝ ↦ Real.exp (-u * x))
      (ENNReal.ofReal (1 - d.mass) • Measure.dirac 0) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  refine ⟨by simpa only [measure] using hatom.add_measure hint, ?_⟩
  rw [measure, integral_add_measure hatom hint, integral_smul_measure, integral_dirac,
    hmoment]
  have hm : d.mass ≤ 1 := by simpa [mass] using d.initial_mass_le
  simp [ENNReal.toReal_ofReal (sub_nonneg.mpr hm)]

/-- Integrability and the resolvent formula for the Laplace transform of a phase-type
law. -/
theorem laplace_transform (u : ℝ) (hu : 0 ≤ u) :
    Integrable (fun x : ℝ ↦ Real.exp (-u * x)) d.measure ∧
      ∫ x, Real.exp (-u * x) ∂d.measure =
        1 - d.mass + d.rate / (d.rate + u) *
          dotProduct d.initial
            (((1 - (d.rate / (d.rate + u)) • d.transition)⁻¹).mulVec d.exit) := by
  have hden : 0 < d.rate + u := by linarith [d.rate_pos]
  have hc0 : 0 ≤ d.rate / (d.rate + u) := div_nonneg d.rate_pos.le hden.le
  have hc1 : d.rate / (d.rate + u) ≤ 1 := (div_le_one hden).mpr (by linarith)
  exact d.measure_laplace_of_hasSum u _ hu (d.hasSum_weight_power _ hc0 hc1)

/-- The Laplace kernel is integrable under every finite phase-type law. -/
theorem integrable_exp_neg_mul_measure (u : ℝ) (hu : 0 ≤ u) :
    Integrable (fun x : ℝ ↦ Real.exp (-u * x)) d.measure :=
  (d.laplace_transform u hu).1

/-- Resolvent formula for the Laplace transform of a phase-type law. -/
theorem integral_exp_neg_mul_measure (u : ℝ) (hu : 0 ≤ u) :
    ∫ x, Real.exp (-u * x) ∂d.measure =
      1 - d.mass + d.rate / (d.rate + u) *
        dotProduct d.initial
          (((1 - (d.rate / (d.rate + u)) • d.transition)⁻¹).mulVec d.exit) :=
  (d.laplace_transform u hu).2

end SSPRK.PhaseTypeData
