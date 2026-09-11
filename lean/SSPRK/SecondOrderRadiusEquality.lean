import SSPRK.Endpoint
import SSPRK.Proofs.SecondOrderClassification

/-! # Second-order equality at the complete radius

Endpoint feasibility transfers the parameter-level classification to the supremum.
-/

open scoped BigOperators ENNReal

namespace SSPRK

noncomputable section

/-- Every second-order tableau whose complete radius is `2s` is a permuted midpoint tableau. -/
theorem second_order_unique_of_radius_eq {s : ℕ} (hs : 0 < s)
    (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ)
    (hord1 : dotProduct b (ones s) = 1)
    (hord2 : dotProduct b (A.mulVec (ones s)) = 1 / 2)
    (hradius : absoluteMonotonicityRadius A b = ENNReal.ofReal (2 * (s : ℝ))) :
    ∃ e : Fin s ≃ Fin s,
      A.submatrix e e = midpointA s ∧ (fun j ↦ b (e j)) = midpointB s := by
  have htwice_pos : 0 < 2 * (s : ℝ) := by positivity
  have hradius_pos : 0 < absoluteMonotonicityRadius A b := by
    rw [hradius, ENNReal.ofReal_pos]
    exact htwice_pos
  have hradius_finite : absoluteMonotonicityRadius A b < ⊤ := by
    rw [hradius]
    exact ENNReal.ofReal_lt_top
  have ham :=
    absolutelyMonotoneAt_absoluteMonotonicityRadius A b hradius_pos hradius_finite
  have hradius_toReal : (absoluteMonotonicityRadius A b).toReal = 2 * (s : ℝ) := by
    rw [hradius, ENNReal.toReal_ofReal htwice_pos.le]
  rw [hradius_toReal] at ham
  exact second_order_classification_at_bound hs A b hord1 hord2 ham

end

end SSPRK
