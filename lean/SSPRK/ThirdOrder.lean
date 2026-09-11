import SSPRK.PhaseTypeThirdMomentIntegral
import SSPRK.RKThirdMoment

/-!
# The general third-order SSP upper bound

The first three chain order conditions fix the first three PH integral moments.
The state-count inequality bounds every positive feasible parameter, and taking the
supremum gives the bound for the complete tableau radius.
-/

namespace SSPRK

/-- The sharp third-order upper bound holds for every real tableau and positive feasible radius. -/
theorem third_order_rk_ssp_bound {s : ℕ} (hs : 2 ≤ s)
    (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ)
    {r : ℝ} (hr : 0 < r) (h : AbsolutelyMonotoneAt A b r)
    (hord1 : dotProduct b (fun _ ↦ (1 : ℝ)) = 1)
    (hord2 : dotProduct b (A.mulVec (fun _ ↦ (1 : ℝ))) = 1 / 2)
    (hord3 : dotProduct b ((A * A).mulVec (fun _ ↦ (1 : ℝ))) = 1 / 6) :
    r ≤ (s : ℝ) - 1 + Real.sqrt ((s : ℝ) ^ 2 - 1) := by
  have hmean : 0 < ∫ x, x ∂(h.phaseType hr).measure := by
    rw [h.phaseType_integral_id hr hord1]
    exact hr
  have hbound := (h.phaseType hr).third_moment_lower_bound hmean
  rw [h.phaseType_integral_id hr hord1, h.phaseType_integral_sq hr hord1 hord2,
    h.phaseType_integral_cube hr hord1 hord2 hord3] at hbound
  apply third_order_bound_of_quadratic (by exact_mod_cast (show 1 ≤ s by omega))
  exact third_order_quadratic_of_moment_bound hr hbound

/-- The third-order bound extends to the full supremum defining the complete SSP radius. -/
theorem third_order_radius_bound {s : ℕ} (hs : 2 ≤ s)
    (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ)
    (hord1 : dotProduct b (fun _ ↦ (1 : ℝ)) = 1)
    (hord2 : dotProduct b (A.mulVec (fun _ ↦ (1 : ℝ))) = 1 / 2)
    (hord3 : dotProduct b ((A * A).mulVec (fun _ ↦ (1 : ℝ))) = 1 / 6) :
    absoluteMonotonicityRadius A b ≤
      ENNReal.ofReal ((s : ℝ) - 1 + Real.sqrt ((s : ℝ) ^ 2 - 1)) := by
  apply iSup_le
  intro r
  apply iSup_le
  intro hr
  apply ENNReal.ofReal_le_ofReal
  rcases hr with rfl | ⟨hr, h⟩
  · have hs' : (2 : ℝ) ≤ s := by exact_mod_cast hs
    linarith [Real.sqrt_nonneg ((s : ℝ) ^ 2 - 1)]
  · exact third_order_rk_ssp_bound hs A b hr h hord1 hord2 hord3

end SSPRK
