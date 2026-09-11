import SecondOrderBound
import SSPRK.SSPRadius

/-! # The complete second-order radius bound -/

namespace SSPRK

open scoped ENNReal

/-- Every feasible radius of a second-order tableau is at most twice the stage count. -/
theorem feasibleRadii_le_second_order {s : ℕ} (hs : 0 < s)
    (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ)
    (hord1 : dotProduct b (fun _ ↦ (1 : ℝ)) = 1)
    (hord2 : dotProduct b (Matrix.mulVec A (fun _ ↦ (1 : ℝ))) = 1 / 2)
    {r : ℝ} (hr : r ∈ feasibleRadii A b) : r ≤ 2 * (s : ℝ) := by
  rcases hr with rfl | ⟨hr, h⟩
  · positivity
  · exact second_order_rk_ssp_bound s hs A b r hr h.det_ne_zero hord1 hord2
      h.stages h.matrix_nonneg h.output_nonneg h.output_mass

/-- The second-order upper bound for the full supremum radius in Theorem 5.2. -/
theorem second_order_radius_bound {s : ℕ} (hs : 0 < s)
    (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ)
    (hord1 : dotProduct b (fun _ ↦ (1 : ℝ)) = 1)
    (hord2 : dotProduct b (Matrix.mulVec A (fun _ ↦ (1 : ℝ))) = 1 / 2) :
    absoluteMonotonicityRadius A b ≤ ENNReal.ofReal (2 * (s : ℝ)) := by
  apply iSup_le
  intro r
  apply iSup_le
  intro hr
  exact ENNReal.ofReal_le_ofReal (feasibleRadii_le_second_order hs A b hord1 hord2 hr)

end SSPRK
