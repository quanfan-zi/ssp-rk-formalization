import SSPRK.Endpoint
import SSPRK.Proofs.ThirdOrderClassification

/-! # Third-order equality at the complete radius

Endpoint feasibility transfers the parameter-level classification to the supremum.
-/

open scoped BigOperators ENNReal

namespace SSPRK

noncomputable section

theorem third_order_unique_of_radius_eq {s : ℕ} (hs : 2 ≤ s)
    (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ)
    (hord1 : dotProduct b (fun _ ↦ (1 : ℝ)) = 1)
    (hord2 : dotProduct b (A.mulVec (fun _ ↦ (1 : ℝ))) = 1 / 2)
    (hord3 : dotProduct b ((A * A).mulVec (fun _ ↦ (1 : ℝ))) = 1 / 6)
    (hradius : absoluteMonotonicityRadius A b = ENNReal.ofReal (thirdOrderRadius s)) :
    ∃ e : Fin s ≃ Fin s,
      A.submatrix e e = sdirkA s ∧ (fun j ↦ b (e j)) = sdirkB s := by
  have hrpos : 0 < thirdOrderRadius s := thirdOrderRadius_pos hs
  have hradius_pos : 0 < absoluteMonotonicityRadius A b := by
    rw [hradius, ENNReal.ofReal_pos]
    exact hrpos
  have hradius_finite : absoluteMonotonicityRadius A b < ⊤ := by
    rw [hradius]
    exact ENNReal.ofReal_lt_top
  have ham := absolutelyMonotoneAt_absoluteMonotonicityRadius A b hradius_pos hradius_finite
  have hradius_toReal : (absoluteMonotonicityRadius A b).toReal = thirdOrderRadius s := by
    rw [hradius, ENNReal.toReal_ofReal hrpos.le]
  rw [hradius_toReal] at ham
  exact third_order_classification_at_bound hs A b hord1 hord2 hord3 ham

end

end SSPRK
