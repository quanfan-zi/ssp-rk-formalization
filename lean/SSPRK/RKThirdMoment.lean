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

end SSPRK
