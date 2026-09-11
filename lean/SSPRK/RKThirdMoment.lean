import SSPRK.RKPhaseType
import SSPRK.PhaseTypeAllMoments
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The third moment of the RK phase-type law

The chain order condition determines the third integral moment of the transformed law.
The scalar consequence of the PH third-moment bound is the sharp quadratic bound on
every positive feasible radius.
-/

open MeasureTheory

namespace SSPRK

namespace AbsolutelyMonotoneAt

variable {s : ℕ} {A : Matrix (Fin s) (Fin s) ℝ} {b : Fin s → ℝ} {r : ℝ}

/-- The first three chain order conditions give the actual third PH integral moment. -/
theorem phaseType_integral_cube (h : AbsolutelyMonotoneAt A b r) (hr : 0 < r)
    (hord1 : dotProduct b (fun _ ↦ (1 : ℝ)) = 1)
    (hord2 : dotProduct b (A.mulVec (fun _ ↦ (1 : ℝ))) = 1 / 2)
    (hord3 : dotProduct b ((A * A).mulVec (fun _ ↦ (1 : ℝ))) = 1 / 6) :
    ∫ x, x ^ 3 ∂(h.phaseType hr).measure = r ^ 3 + 6 * r ^ 2 + 6 * r := by
  rw [(h.phaseType hr).integral_pow_measure 3 (by norm_num), h.phaseType_green hr]
  norm_num only [phaseType, Nat.factorial_succ, Nat.factorial_zero, Nat.cast_ofNat,
    one_pow, div_one]
  rw [pow_succ, pow_two, Matrix.dotProduct_mulVec]
  have hm := rkOmega_N_cu_ones_eq r b A h.det_ne_zero hord1 hord2 hord3
  change dotProduct (Matrix.vecMul (rkOmega r b A) (rkN r A * rkN r A * rkN r A))
    (fun _ ↦ 1) = _ at hm
  nlinarith only [hm]

end AbsolutelyMonotoneAt

/-- Substitute the RK moments into the PH bound and cancel the positive squared mean. -/
theorem third_order_quadratic_of_moment_bound {s r : ℝ} (hr : 0 < r)
    (hbound : (s + 2) * (r ^ 2 + 2 * r) ^ 2 ≤
      (s + 1) * r * (r ^ 3 + 6 * r ^ 2 + 6 * r)) :
    r ^ 2 - 2 * (s - 1) * r - 2 * (s - 1) ≤ 0 := by
  apply nonpos_of_mul_nonpos_left (b := r ^ 2) _ (sq_pos_of_pos hr)
  nlinarith only [hbound]

/-- The positive root of the RK moment quadratic gives the third-order radius bound. -/
theorem third_order_bound_of_quadratic {s r : ℝ} (hs : 1 ≤ s)
    (hquad : r ^ 2 - 2 * (s - 1) * r - 2 * (s - 1) ≤ 0) :
    r ≤ s - 1 + Real.sqrt (s ^ 2 - 1) := by
  have hdisc : 0 ≤ s ^ 2 - 1 := by nlinarith only [hs]
  have hroot := Real.sq_sqrt hdisc
  have hnonneg := Real.sqrt_nonneg (s ^ 2 - 1)
  by_contra! h
  nlinarith only [hquad, hroot, hnonneg, h]

end SSPRK
