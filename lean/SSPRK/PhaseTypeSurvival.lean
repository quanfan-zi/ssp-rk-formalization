import SSPRK.PhaseTypeDensity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Survival functions and cumulative probabilities of finite phase-type laws. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace SSPRK.PhaseTypeData

variable {s : ℕ} (d : PhaseTypeData s)

noncomputable def matrixSurvival (t : ℝ) : ℝ :=
  dotProduct d.initial ((NormedSpace.exp (t • d.generator)).mulVec (fun _ ↦ 1))

noncomputable def matrixDensity (t : ℝ) : ℝ :=
  dotProduct d.initial ((NormedSpace.exp (t • d.generator)).mulVec
    ((-d.generator).mulVec (fun _ ↦ 1)))

open scoped Matrix.Norms.Operator in
theorem hasDerivAt_exp_pairing (v : Fin s → ℝ) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ dotProduct d.initial
      ((NormedSpace.exp (u • d.generator)).mulVec v))
      (dotProduct d.initial
        ((NormedSpace.exp (t • d.generator) * d.generator).mulVec v)) t := by
  have h := hasDerivAt_exp_smul_const d.generator t
  unfold Matrix.mulVec dotProduct
  exact HasDerivAt.fun_sum (fun i _ ↦
    (HasDerivAt.fun_sum (fun j _ ↦
      ((hasDerivAt_pi.mp (hasDerivAt_pi.mp h i) j).mul_const (v j)))).const_mul (d.initial i))

theorem hasDerivAt_matrixSurvival (t : ℝ) :
    HasDerivAt d.matrixSurvival (-d.matrixDensity t) t := by
  convert d.hasDerivAt_exp_pairing (fun _ ↦ 1) t using 1
  simp only [matrixDensity, Matrix.mulVec_mulVec, Matrix.neg_mulVec, Matrix.mulVec_neg,
    dotProduct_neg, neg_neg]

theorem continuous_matrixDensity : Continuous d.matrixDensity := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (d.hasDerivAt_exp_pairing ((-d.generator).mulVec (fun _ ↦ 1)) t).continuousAt

theorem matrixSurvival_zero : d.matrixSurvival 0 = d.mass := by
  simp [matrixSurvival, mass, dotProduct]

theorem integral_matrixDensity (t : ℝ) :
    ∫ x in (0 : ℝ)..t, d.matrixDensity x = d.mass - d.matrixSurvival t := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u ↦ -d.matrixSurvival u) (f' := d.matrixDensity)
    (fun u _ ↦ by simpa only [neg_neg] using (d.hasDerivAt_matrixSurvival u).neg)
    (d.continuous_matrixDensity.intervalIntegrable 0 t)
  dsimp only at h
  rw [d.matrixSurvival_zero] at h
  convert h using 1
  ring

theorem measure_Ioc_eq_lintegral_matrixDensity (t : ℝ) :
    d.measure (Ioc 0 t) = ∫⁻ x in Ioc 0 t, ENNReal.ofReal (d.matrixDensity x) := by
  rw [d.measure_eq_atom_add_withDensity_generator, Measure.add_apply, Measure.smul_apply]
  simp only [Measure.dirac_apply' _ measurableSet_Ioc, indicator_apply, mem_Ioc,
    lt_self_iff_false, false_and, if_false, smul_eq_mul, mul_zero, zero_add]
  rw [withDensity_apply _ measurableSet_Ioc]
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro x hx
  dsimp only
  rw [if_pos hx.1.le]
  rfl

theorem measureReal_Ioc_eq_integral_matrixDensity (t : ℝ) :
    d.measure.real (Ioc 0 t) = ∫ x in Ioc 0 t, d.matrixDensity x := by
  rw [measureReal_def, d.measure_Ioc_eq_lintegral_matrixDensity]
  symm
  apply integral_eq_lintegral_of_nonneg_ae
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
    exact d.generator_density_nonneg hx.1.le
  · exact d.continuous_matrixDensity.aestronglyMeasurable

theorem measureReal_Ioc_eq_mass_sub_survival {t : ℝ} (ht : 0 ≤ t) :
    d.measure.real (Ioc 0 t) = d.mass - d.matrixSurvival t := by
  rw [d.measureReal_Ioc_eq_integral_matrixDensity,
    ← intervalIntegral.integral_of_le ht, d.integral_matrixDensity]

theorem measureReal_Iic_eq_one_sub_survival {t : ℝ} (ht : 0 ≤ t) :
    d.measure.real (Iic t) = 1 - d.matrixSurvival t := by
  rw [← Iic_union_Ioc_eq_Iic ht, measureReal_union (by
    apply disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge hx) hy.1) measurableSet_Ioc,
    d.measureReal_Ioc_eq_mass_sub_survival ht]
  have hzero : d.measure.real (Iic 0) = 1 - d.mass := by
    rw [measureReal_def, d.measure_apply_Iic_zero, ENNReal.toReal_ofReal]
    exact sub_nonneg.mpr d.initial_mass_le
  rw [hzero]
  ring

theorem measureReal_Ioi_eq_matrixSurvival {t : ℝ} (ht : 0 ≤ t) :
    d.measure.real (Ioi t) = d.matrixSurvival t := by
  have h := measureReal_add_measureReal_compl (μ := d.measure) (s := Iic t) measurableSet_Iic
  have huniv : d.measure.real univ = 1 := by simp [measureReal_def]
  rw [compl_Iic, huniv, d.measureReal_Iic_eq_one_sub_survival ht] at h
  linarith

theorem matrixSurvival_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ d.matrixSurvival t := by
  rw [← d.measureReal_Ioi_eq_matrixSurvival ht]
  exact measureReal_nonneg

theorem matrixSurvival_le_mass {t : ℝ} (ht : 0 ≤ t) : d.matrixSurvival t ≤ d.mass := by
  have h : 0 ≤ d.measure.real (Ioc 0 t) := measureReal_nonneg
  rw [d.measureReal_Ioc_eq_mass_sub_survival ht] at h
  linarith

/-- The probability of survival beyond a nonnegative time is the matrix exponential row sum. -/
theorem measure_Ioi_eq_exp {t : ℝ} (ht : 0 ≤ t) :
    d.measure (Ioi t) = ENNReal.ofReal
      (dotProduct d.initial ((NormedSpace.exp (t • d.generator)).mulVec (fun _ ↦ 1))) := by
  calc
    d.measure (Ioi t) = ENNReal.ofReal (d.measure.real (Ioi t)) :=
      (ENNReal.ofReal_toReal (by finiteness)).symm
    _ = _ := by rw [d.measureReal_Ioi_eq_matrixSurvival ht]; rfl

/-- Real-valued form of the PH survival formula. -/
theorem measureReal_Ioi_eq_exp {t : ℝ} (ht : 0 ≤ t) :
    d.measure.real (Ioi t) =
      dotProduct d.initial ((NormedSpace.exp (t • d.generator)).mulVec (fun _ ↦ 1)) :=
  d.measureReal_Ioi_eq_matrixSurvival ht

/-- The CDF is one minus the transient matrix-exponential row sum at nonnegative times. -/
theorem cdf_eq_one_sub_exp {t : ℝ} (ht : 0 ≤ t) :
    cdf d.measure t =
      1 - dotProduct d.initial ((NormedSpace.exp (t • d.generator)).mulVec (fun _ ↦ 1)) := by
  rw [cdf_eq_real]
  exact d.measureReal_Iic_eq_one_sub_survival ht

end SSPRK.PhaseTypeData
