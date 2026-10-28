import SSPRK.AuxiliaryScale
import SSPRK.ScaledExponential
import SSPRK.MomentClassOperations
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The auxiliary probability law in state elimination

A two-point mixture of scaled exponential laws realizes the three auxiliary moments.
The zero scale is allowed and contributes an atom at zero.
-/

open MeasureTheory

namespace SSPRK

/-- The mixture of two scaled unit-rate exponential laws. -/
noncomputable def binaryScaledExponential (p q lo hi : ℝ) : Measure ℝ :=
  ENNReal.ofReal p • scaledExponentialLaw lo + ENNReal.ofReal q • scaledExponentialLaw hi

/-- Nonnegative weights of total mass one give a probability law. -/
theorem binaryScaledExponential_probability {p q lo hi : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hsum : p + q = 1) :
    IsProbabilityMeasure (binaryScaledExponential p q lo hi) where
  measure_univ := by
    simp only [binaryScaledExponential, Measure.add_apply, Measure.smul_apply,
      measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hp hq, hsum, ENNReal.ofReal_one]

/-- All natural moments of a two-component scaled exponential mixture are integrable. -/
theorem binaryScaledExponential_integrable_pow (p q lo hi : ℝ) (k : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ k) (binaryScaledExponential p q lo hi) := by
  exact ((integrable_pow_scaledExponentialLaw lo k).smul_measure ENNReal.ofReal_ne_top).add_measure
    ((integrable_pow_scaledExponentialLaw hi k).smul_measure ENNReal.ofReal_ne_top)

/-- The factorial moment formula holds for the two-component mixture. -/
theorem binaryScaledExponential_integral_pow {p q lo hi : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (k : ℕ) :
    ∫ x, x ^ k ∂binaryScaledExponential p q lo hi =
      (k.factorial : ℝ) * (p * lo ^ k + q * hi ^ k) := by
  rw [binaryScaledExponential, integral_add_measure
    ((integrable_pow_scaledExponentialLaw lo k).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_pow_scaledExponentialLaw hi k).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hq,
    smul_eq_mul, integral_pow_scaledExponentialLaw]
  ring

/-- Nonnegative component scales give nonnegative support. -/
theorem binaryScaledExponential_nonneg {p q lo hi : ℝ}
    (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) :
    ∀ᵐ x ∂binaryScaledExponential p q lo hi, 0 ≤ x := by
  apply ae_add_measure_iff.mpr
  constructor
  · exact Measure.ae_smul_measure (ae_nonneg_scaledExponentialLaw hlo) _
  · exact Measure.ae_smul_measure (ae_nonneg_scaledExponentialLaw hhi) _

/-- A nonnegative probability law realizes all three prescribed auxiliary moments.
-/
theorem exists_auxiliary_probability (η1 η2 : ℝ) (hη1 : 0 ≤ η1) (hη2 : 0 ≤ η2)
    (hzero : η1 = 0 → η2 = 0) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ (∀ᵐ x ∂μ, 0 ≤ x) ∧
      (∀ k : ℕ, Integrable (fun x : ℝ ↦ x ^ k) μ) ∧
      (∫ x, x ∂μ) = 1 ∧ (∫ x, x ^ 2 ∂μ) = 2 * (1 + η1) ∧
      (∫ x, x ^ 3 ∂μ) = 6 * (1 + η1) ^ 2 + 3 * η2 := by
  obtain ⟨lo, hi, p, q, hlo, hhi, hp, hq, hsum, hfirst, hsecond, hthird⟩ :=
    exists_auxiliary_scale η1 η2 hη1 hη2 hzero
  refine ⟨binaryScaledExponential p q lo hi,
    binaryScaledExponential_probability hp hq hsum,
    binaryScaledExponential_nonneg hlo hhi,
    binaryScaledExponential_integrable_pow p q lo hi, ?_, ?_, ?_⟩
  · simpa only [pow_one, Nat.factorial_one, Nat.cast_one, one_mul, hfirst] using
      (binaryScaledExponential_integral_pow (lo := lo) (hi := hi) hp hq 1)
  · rw [binaryScaledExponential_integral_pow hp hq 2, hsecond]
    norm_num
  · rw [binaryScaledExponential_integral_pow hp hq 3, hthird]
    norm_num
    ring

end SSPRK
