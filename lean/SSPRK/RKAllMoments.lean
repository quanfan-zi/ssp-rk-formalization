import SSPRK.PaperRKPH
import Mathlib.Data.Nat.Choose.Sum

/-!
# The all-order RK/PH moment dictionary

The matrix identity for the transformed output row removes one Green factor.
The binomial theorem then converts chain order conditions into the finite sum
in Proposition 3.2 of V2.10.
-/

open MeasureTheory
open scoped BigOperators

namespace SSPRK

/-- One Green factor cancels the inverse in the transformed output row. -/
theorem rkOmega_vecMul_rkN_pow_succ {s : ℕ} (r : ℝ) (b : Fin s → ℝ)
    (A : Matrix (Fin s) (Fin s) ℝ) (hinv : (rkN r A).det ≠ 0) (k : ℕ) :
    Matrix.vecMul (rkOmega r b A) (rkN r A ^ (k + 1)) =
      r • Matrix.vecMul b (rkN r A ^ k) := by
  rw [pow_succ', ← Matrix.vecMul_vecMul, rkOmega_vecMul_rkN r b A hinv,
    Matrix.smul_vecMul]

/-- Expanding the shifted matrix gives the chain-weighted binomial sum. -/
theorem rkN_pow_weighted_binomial {s : ℕ} (r : ℝ) (b : Fin s → ℝ)
    (A : Matrix (Fin s) (Fin s) ℝ) (k : ℕ) :
    dotProduct b ((rkN r A ^ k).mulVec (fun _ ↦ 1)) =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * r ^ j *
        dotProduct b ((A ^ j).mulVec (fun _ ↦ 1)) := by
  rw [rkN, add_comm, (Commute.one_right (r • A)).add_pow]
  simp only [one_pow, mul_one, smul_pow, Matrix.sum_mulVec, dotProduct_sum]
  simp [← Matrix.mulVec_mulVec, Matrix.natCast_mulVec, Matrix.smul_mulVec,
    Matrix.mulVec_smul, dotProduct_smul, mul_comm, mul_assoc]

end SSPRK

namespace SSPRK.AbsolutelyMonotoneAt

/-- Every positive normalized RK/PH moment is a shifted RK matrix power. -/
theorem normalizedPhaseType_integral_pow {s : ℕ} {A : Matrix (Fin s) (Fin s) ℝ}
    {b : Fin s → ℝ} {r : ℝ} (h : AbsolutelyMonotoneAt A b r) (hr : 0 < r)
    (hord1 : dotProduct b (fun _ ↦ (1 : ℝ)) = 1) (k : ℕ) (hk : 0 < k) :
    ∫ x, x ^ k ∂(h.normalizedPhaseType hr hord1).measure =
      (k.factorial : ℝ) * r / rkSigma r b A *
        dotProduct b ((rkN r A ^ (k - 1)).mulVec (fun _ ↦ 1)) := by
  simp only [(h.normalizedPhaseType hr hord1).integral_pow_measure k hk,
    normalizedPhaseType_initial, normalizedPhaseType_green, normalizedPhaseType_rate,
    one_pow, div_one, Matrix.dotProduct_mulVec]
  have hpower : Matrix.vecMul (rkOmega r b A) (rkN r A ^ k) =
      r • Matrix.vecMul b (rkN r A ^ (k - 1)) := by
    simpa only [Nat.sub_add_cancel hk] using
      rkOmega_vecMul_rkN_pow_succ r b A h.det_ne_zero (k - 1)
  simp [Matrix.smul_vecMul, hpower, smul_dotProduct, smul_eq_mul, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm]

end SSPRK.AbsolutelyMonotoneAt
