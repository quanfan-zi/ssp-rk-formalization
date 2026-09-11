import SSPRK.PhaseType
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-! Matrix-exponential densities of the phase-type probability measures. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace SSPRK.PhaseTypeData

variable {s : ℕ} (d : PhaseTypeData s)

theorem erlang_pdf_real (n : ℕ) (t : ℝ) :
    gammaPDFReal (n + 1) d.rate t = if 0 ≤ t then
      d.rate * Real.exp (-(d.rate * t)) * ((d.rate * t) ^ n / n.factorial) else 0 := by
  rw [gammaPDFReal, Real.Gamma_nat_eq_factorial,
    show (n : ℝ) + 1 - 1 = n by ring, Real.rpow_natCast,
    Real.rpow_add d.rate_pos, Real.rpow_natCast, Real.rpow_one]
  split_ifs <;> simp only [mul_pow]; ring

open scoped Matrix.Norms.Operator in
theorem hasSum_uniformized_density (t : ℝ) :
    HasSum (fun n : ℕ ↦ d.rate * Real.exp (-(d.rate * t)) *
      ((d.rate * t) ^ n / n.factorial) * d.weight n)
      (d.rate * Real.exp (-(d.rate * t)) * dotProduct d.initial
        ((NormedSpace.exp ((d.rate * t) • d.transition)).mulVec d.exit)) := by
  have h := d.hasSum_pairing
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ((d.rate * t) • d.transition)) d.exit
  have hscaled := h.mul_left (d.rate * Real.exp (-(d.rate * t)))
  convert hscaled using 1
  funext n
  simp only [smul_pow, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, weight]
  ring

theorem tsum_erlang_density (t : ℝ) :
    (∑' n : ℕ, ENNReal.ofReal (d.weight n) * gammaPDF (n + 1) d.rate t) =
      if 0 ≤ t then ENNReal.ofReal (d.rate * Real.exp (-(d.rate * t)) *
        dotProduct d.initial ((NormedSpace.exp ((d.rate * t) • d.transition)).mulVec d.exit))
      else 0 := by
  by_cases ht : 0 ≤ t
  · rw [if_pos ht]
    have hterm (n : ℕ) : ENNReal.ofReal (d.weight n) * gammaPDF (n + 1) d.rate t =
        ENNReal.ofReal (d.rate * Real.exp (-(d.rate * t)) *
          ((d.rate * t) ^ n / n.factorial) * d.weight n) := by
      rw [gammaPDF, d.erlang_pdf_real, if_pos ht, ← ENNReal.ofReal_mul (d.weight_nonneg n)]
      congr 1
      ring
    simp_rw [hterm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity [d.rate_pos, d.weight_nonneg n])
      (d.hasSum_uniformized_density t).summable, (d.hasSum_uniformized_density t).tsum_eq]
  · simp only [if_neg ht, gammaPDF_of_neg (lt_of_not_ge ht), mul_zero, tsum_zero]

theorem positiveMeasure_eq_withDensity_erlang :
    d.positiveMeasure = volume.withDensity
      (fun t ↦ ∑' n : ℕ, ENNReal.ofReal (d.weight n) * gammaPDF (n + 1) d.rate t) := by
  have hm (n : ℕ) : Measurable (gammaPDF (n + 1) d.rate) :=
    (measurable_gammaPDFReal (n + 1) d.rate).ennreal_ofReal
  calc
    d.positiveMeasure = Measure.sum (fun n : ℕ ↦ volume.withDensity
        (ENNReal.ofReal (d.weight n) • gammaPDF (n + 1) d.rate)) := by
      unfold positiveMeasure gammaMeasure
      congr 1
      funext n
      exact (withDensity_smul _ (hm n)).symm
    _ = volume.withDensity (∑' n : ℕ,
        ENNReal.ofReal (d.weight n) • gammaPDF (n + 1) d.rate) :=
      (withDensity_tsum (fun n ↦ (hm n).const_smul _)).symm
    _ = _ := by
      congr 1
      funext t
      exact tsum_apply (Pi.summable.mpr (fun _ ↦ ENNReal.summable))

theorem positiveMeasure_eq_withDensity_uniformized :
    d.positiveMeasure = volume.withDensity (fun t ↦ if 0 ≤ t then
      ENNReal.ofReal (d.rate * Real.exp (-(d.rate * t)) *
        dotProduct d.initial ((NormedSpace.exp ((d.rate * t) • d.transition)).mulVec d.exit))
      else 0) := by
  rw [d.positiveMeasure_eq_withDensity_erlang]
  congr 1
  funext t
  exact d.tsum_erlang_density t

open scoped Matrix.Norms.Operator in
theorem exp_scalar_one (x : ℝ) :
    NormedSpace.exp (x • (1 : Matrix (Fin s) (Fin s) ℝ)) =
      Real.exp x • (1 : Matrix (Fin s) (Fin s) ℝ) := by
  simpa only [Algebra.algebraMap_eq_smul_one, ← Real.exp_eq_exp_ℝ] using
    (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := Matrix (Fin s) (Fin s) ℝ) x).symm

theorem exp_generator_uniformization (t : ℝ) :
    NormedSpace.exp (t • d.generator) =
      Real.exp (-(d.rate * t)) • NormedSpace.exp ((d.rate * t) • d.transition) := by
  have hid : t • d.generator = (-(d.rate * t)) • (1 : Matrix (Fin s) (Fin s) ℝ) +
      (d.rate * t) • d.transition := by
    unfold generator
    module
  rw [hid, Matrix.exp_add_of_commute _ _ ((Commute.one_left _).smul_left _),
    exp_scalar_one, smul_mul_assoc, Matrix.one_mul]

theorem neg_generator_mulVec_one :
    (-d.generator).mulVec (fun _ ↦ 1) = d.rate • d.exit := by
  have hid : -d.generator = d.rate • (1 - d.transition) := by
    unfold generator
    module
  rw [hid, Matrix.smul_mulVec]
  rfl

theorem generator_density_eq_uniformized (t : ℝ) :
    dotProduct d.initial ((NormedSpace.exp (t • d.generator)).mulVec
      ((-d.generator).mulVec (fun _ ↦ 1))) =
      d.rate * Real.exp (-(d.rate * t)) * dotProduct d.initial
        ((NormedSpace.exp ((d.rate * t) • d.transition)).mulVec d.exit) := by
  rw [d.exp_generator_uniformization, d.neg_generator_mulVec_one]
  simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  ring

/-- The real matrix-exponential density is nonnegative on nonnegative times. -/
theorem generator_density_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ dotProduct d.initial ((NormedSpace.exp (t • d.generator)).mulVec
      ((-d.generator).mulVec (fun _ ↦ 1))) := by
  rw [d.generator_density_eq_uniformized, ← (d.hasSum_uniformized_density t).tsum_eq]
  exact tsum_nonneg (fun n ↦ by positivity [d.rate_pos, d.weight_nonneg n])

/-- The positive-time PH law has the classical matrix-exponential density. -/
theorem positiveMeasure_eq_withDensity_generator :
    d.positiveMeasure = volume.withDensity (fun t ↦ if 0 ≤ t then
      ENNReal.ofReal (dotProduct d.initial ((NormedSpace.exp (t • d.generator)).mulVec
        ((-d.generator).mulVec (fun _ ↦ 1)))) else 0) := by
  simp only [d.generator_density_eq_uniformized]
  exact d.positiveMeasure_eq_withDensity_uniformized

/-- The full PH law consists of the immediate-absorption atom and the exponential density. -/
theorem measure_eq_atom_add_withDensity_generator :
    d.measure = ENNReal.ofReal (1 - d.mass) • Measure.dirac 0 +
      volume.withDensity (fun t ↦ if 0 ≤ t then ENNReal.ofReal
        (dotProduct d.initial ((NormedSpace.exp (t • d.generator)).mulVec
          ((-d.generator).mulVec (fun _ ↦ 1)))) else 0) := by
  rw [measure, d.positiveMeasure_eq_withDensity_generator]

end SSPRK.PhaseTypeData
