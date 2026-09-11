import SSPRK.SecondOrder
import Mathlib.Data.ENNReal.Real

/-!
# Complete absolute-monotonicity radius

The feasible set and its supremum from V1.6, Section 2.4. The second-order theorem bounds
every positive feasible parameter, and hence bounds the full tableau radius.
-/

namespace SSPRK

open scoped ENNReal

/-- The complete tableau inequalities at a parameter, with positivity imposed separately. -/
structure AbsolutelyMonotoneAt {s : ℕ} (A : Matrix (Fin s) (Fin s) ℝ)
    (b : Fin s → ℝ) (r : ℝ) : Prop where
  det_ne_zero : (1 + r • A).det ≠ 0
  stages : 0 ≤ Matrix.mulVec ((1 + r • A)⁻¹) (fun _ ↦ (1 : ℝ))
  matrix_nonneg : ∀ i j : Fin s, 0 ≤ (r • (A * (1 + r • A)⁻¹)) i j
  output_nonneg : 0 ≤ Matrix.vecMul b ((1 + r • A)⁻¹)
  output_mass : 0 ≤ 1 - r * dotProduct
    (Matrix.vecMul b ((1 + r • A)⁻¹)) (fun _ ↦ (1 : ℝ))

/-- Zero together with the positive feasible parameters. -/
def feasibleRadii {s : ℕ} (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ) : Set ℝ :=
  {r | r = 0 ∨ 0 < r ∧ AbsolutelyMonotoneAt A b r}

/-- The complete absolute-monotonicity radius, allowing an infinite feasible interval. -/
noncomputable def absoluteMonotonicityRadius {s : ℕ}
    (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ) : ℝ≥0∞ :=
  ⨆ r ∈ feasibleRadii A b, ENNReal.ofReal r

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
