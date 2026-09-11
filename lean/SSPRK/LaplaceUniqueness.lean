import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Uniqueness of Laplace transforms on the nonnegative half-line

A positive exponential tilt gives a measure whose complex moment-generating function
is analytic on a strip containing the imaginary axis. Equality of the original
Laplace transforms propagates across that strip and hence identifies characteristic
functions.
-/

open MeasureTheory Set Filter Real Complex

open scoped ENNReal Topology

namespace MeasureTheory.Measure

private noncomputable def laplaceTiltDensity (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-x))

private lemma measurable_laplaceTiltDensity : Measurable laplaceTiltDensity := by
  unfold laplaceTiltDensity
  fun_prop

@[simp]
private lemma laplaceTiltDensity_toReal (x : ℝ) :
    (laplaceTiltDensity x).toReal = Real.exp (-x) := by
  simp [laplaceTiltDensity, (Real.exp_pos _).le]

private lemma laplaceTiltDensity_ne_zero (x : ℝ) : laplaceTiltDensity x ≠ 0 := by
  exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

private lemma laplaceTiltDensity_ne_top (x : ℝ) : laplaceTiltDensity x ≠ ∞ := by
  simp [laplaceTiltDensity]

private lemma isFiniteMeasure_withDensity_laplaceTilt {μ : Measure ℝ}
    [IsFiniteMeasure μ] (hμ : ∀ᵐ x ∂μ, 0 ≤ x) :
    IsFiniteMeasure (μ.withDensity laplaceTiltDensity) := by
  apply isFiniteMeasure_withDensity
  apply ne_of_lt
  refine lt_of_le_of_lt (lintegral_mono_ae (g := fun _ : ℝ ↦ 1) ?_) ?_
  · filter_upwards [hμ] with x hx
    exact ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx))
  · rw [lintegral_const, one_mul]
    exact measure_lt_top μ univ

private lemma integrable_exp_mul_withDensity_laplaceTilt {μ : Measure ℝ}
    [IsFiniteMeasure μ] (hμ : ∀ᵐ x ∂μ, 0 ≤ x) {t : ℝ} (ht : t < 1) :
    Integrable (fun x : ℝ ↦ Real.exp (t * x)) (μ.withDensity laplaceTiltDensity) := by
  rw [integrable_withDensity_iff measurable_laplaceTiltDensity
    (ae_of_all _ fun x ↦ (laplaceTiltDensity_ne_top x).lt_top)]
  simp_rw [laplaceTiltDensity_toReal]
  refine (integrable_const (1 : ℝ)).mono (by fun_prop) ?_
  filter_upwards [hμ] with x hx
  rw [norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
  rw [← Real.exp_add, norm_one]
  refine Real.exp_le_one_iff.mpr ?_
  nlinarith

private lemma mgf_withDensity_laplaceTilt (μ : Measure ℝ) (t : ℝ) :
    ProbabilityTheory.mgf id (μ.withDensity laplaceTiltDensity) t =
      ∫ x, Real.exp (-(1 - t) * x) ∂μ := by
  rw [ProbabilityTheory.mgf,
    integral_withDensity_eq_integral_toReal_smul measurable_laplaceTiltDensity
      (ae_of_all _ fun x ↦ (laplaceTiltDensity_ne_top x).lt_top)]
  simp_rw [id_eq, laplaceTiltDensity_toReal, smul_eq_mul, ← Real.exp_add]
  congr 1
  funext x
  congr 1
  ring

/-- Two finite measures supported on the nonnegative half-line are equal if their
Laplace transforms agree at every nonnegative argument. -/
theorem ext_of_laplace_eq_of_ae_nonneg {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (hν : ∀ᵐ x ∂ν, 0 ≤ x)
    (h_laplace : ∀ u, 0 ≤ u →
      ∫ x, Real.exp (-u * x) ∂μ = ∫ x, Real.exp (-u * x) ∂ν) :
    μ = ν := by
  letI : IsFiniteMeasure (μ.withDensity laplaceTiltDensity) :=
    isFiniteMeasure_withDensity_laplaceTilt hμ
  letI : IsFiniteMeasure (ν.withDensity laplaceTiltDensity) :=
    isFiniteMeasure_withDensity_laplaceTilt hν
  have h_exp_μ : Iio (1 : ℝ) ⊆ ProbabilityTheory.integrableExpSet id
      (μ.withDensity laplaceTiltDensity) := by
    intro t ht
    exact integrable_exp_mul_withDensity_laplaceTilt hμ ht
  have h_exp_ν : Iio (1 : ℝ) ⊆ ProbabilityTheory.integrableExpSet id
      (ν.withDensity laplaceTiltDensity) := by
    intro t ht
    exact integrable_exp_mul_withDensity_laplaceTilt hν ht
  have h_int_μ : Iio (1 : ℝ) ⊆ interior (ProbabilityTheory.integrableExpSet id
      (μ.withDensity laplaceTiltDensity)) :=
    interior_maximal h_exp_μ isOpen_Iio
  have h_int_ν : Iio (1 : ℝ) ⊆ interior (ProbabilityTheory.integrableExpSet id
      (ν.withDensity laplaceTiltDensity)) :=
    interior_maximal h_exp_ν isOpen_Iio
  have h_analytic_μ : AnalyticOnNhd ℂ
      (ProbabilityTheory.complexMGF id (μ.withDensity laplaceTiltDensity))
      {z : ℂ | z.re < 1} :=
    ProbabilityTheory.analyticOnNhd_complexMGF.mono fun z hz ↦ h_int_μ hz
  have h_analytic_ν : AnalyticOnNhd ℂ
      (ProbabilityTheory.complexMGF id (ν.withDensity laplaceTiltDensity))
      {z : ℂ | z.re < 1} :=
    ProbabilityTheory.analyticOnNhd_complexMGF.mono fun z hz ↦ h_int_ν hz
  have h_real (t : ℝ) (ht : t < 1) :
      ProbabilityTheory.complexMGF id (μ.withDensity laplaceTiltDensity) t =
        ProbabilityTheory.complexMGF id (ν.withDensity laplaceTiltDensity) t := by
    rw [ProbabilityTheory.complexMGF_ofReal, ProbabilityTheory.complexMGF_ofReal]
    rw [mgf_withDensity_laplaceTilt, mgf_withDensity_laplaceTilt]
    exact_mod_cast h_laplace (1 - t) (sub_nonneg.mpr ht.le)
  have h_real_frequently : ∃ᶠ t : ℝ in 𝓝[≠] 0,
      ProbabilityTheory.complexMGF id (μ.withDensity laplaceTiltDensity) t =
        ProbabilityTheory.complexMGF id (ν.withDensity laplaceTiltDensity) t := by
    have h_eventually : ∀ᶠ t : ℝ in 𝓝[≠] 0, t < 1 :=
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono inf_le_left
    exact h_eventually.frequently.mono h_real
  have h_complex_frequently : ∃ᶠ z : ℂ in 𝓝[≠] 0,
      ProbabilityTheory.complexMGF id (μ.withDensity laplaceTiltDensity) z =
        ProbabilityTheory.complexMGF id (ν.withDensity laplaceTiltDensity) z := by
    rw [frequently_iff_seq_forall] at h_real_frequently ⊢
    obtain ⟨xs, hx_tendsto, hx_eq⟩ := h_real_frequently
    refine ⟨fun n ↦ xs n, ?_, fun n ↦ ?_⟩
    · rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
      constructor
      · change Tendsto (fun n ↦ (xs n : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ))
        rw [tendsto_ofReal_iff]
        exact hx_tendsto.1
      · simpa using hx_tendsto.2
    · simp [hx_eq]
  have h_complex := AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
    h_analytic_μ h_analytic_ν (convex_halfSpace_re_lt 1).isPreconnected
    (z₀ := (0 : ℂ)) (by norm_num) h_complex_frequently
  have h_char : charFun (μ.withDensity laplaceTiltDensity) =
      charFun (ν.withDensity laplaceTiltDensity) := by
    funext t
    rw [← ProbabilityTheory.complexMGF_id_mul_I,
      ← ProbabilityTheory.complexMGF_id_mul_I]
    exact h_complex (by simp)
  have h_tilt : μ.withDensity laplaceTiltDensity =
      ν.withDensity laplaceTiltDensity :=
    Measure.ext_of_charFun h_char
  calc
    μ = (μ.withDensity laplaceTiltDensity).withDensity
        (fun x ↦ (laplaceTiltDensity x)⁻¹) := by
      symm
      exact withDensity_inv_same measurable_laplaceTiltDensity
        (ae_of_all _ fun x ↦ laplaceTiltDensity_ne_zero x)
        (ae_of_all _ fun x ↦ laplaceTiltDensity_ne_top x)
    _ = (ν.withDensity laplaceTiltDensity).withDensity
        (fun x ↦ (laplaceTiltDensity x)⁻¹) := by rw [h_tilt]
    _ = ν := withDensity_inv_same measurable_laplaceTiltDensity
      (ae_of_all _ fun x ↦ laplaceTiltDensity_ne_zero x)
      (ae_of_all _ fun x ↦ laplaceTiltDensity_ne_top x)

end MeasureTheory.Measure
