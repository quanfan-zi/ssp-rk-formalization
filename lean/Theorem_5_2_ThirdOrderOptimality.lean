import SSPRK.ThirdOrderOptimality
import SSPRK.ThirdOrderRadiusEquality

/-!
# V2.10, Theorem 5.2: third-order optimality and uniqueness

The radius `thirdOrderRadius s` is exactly `s - 1 + sqrt (s^2 - 1)`.
The canonical tableau `sdirkA s`, `sdirkB s` has constant diagonal
`(1 - (s - 1) / sqrt (s^2 - 1)) / 2`, constant strict lower triangle
`1 / sqrt (s^2 - 1)`, zero strict upper triangle, and weights `1 / s`.
For `s ≥ 2` the diagonal equals the paper's
`(1 - sqrt ((s - 1) / (s + 1))) / 2`.
The supremum includes all four classical order-three conditions and all real
tableaux, without a triangularity assumption.

This entry assembles the existing optimality, order, attainment, and classification results.
-/

open scoped ENNReal

namespace SSPRK.Paper

/-- The complete statement of V2.10 Theorem 5.2, including attainment and classification. -/
theorem theorem_5_2 (s : ℕ) (hs : 2 ≤ s) :
    thirdOrderOptimalRadius s =
      ENNReal.ofReal ((s : ℝ) - 1 + Real.sqrt ((s : ℝ) ^ 2 - 1)) ∧
    dotProduct (sdirkB s) (fun _ ↦ (1 : ℝ)) = 1 ∧
    dotProduct (sdirkB s) ((sdirkA s).mulVec (fun _ ↦ (1 : ℝ))) = 1 / 2 ∧
    dotProduct (sdirkB s)
      (fun i ↦ ((sdirkA s).mulVec (fun _ ↦ (1 : ℝ)) i) ^ 2) = 1 / 3 ∧
    dotProduct (sdirkB s) ((sdirkA s * sdirkA s).mulVec (fun _ ↦ (1 : ℝ))) = 1 / 6 ∧
    absoluteMonotonicityRadius (sdirkA s) (sdirkB s) =
      ENNReal.ofReal ((s : ℝ) - 1 + Real.sqrt ((s : ℝ) ^ 2 - 1)) ∧
    (∀ (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ),
      dotProduct b (fun _ ↦ (1 : ℝ)) = 1 →
      dotProduct b (A.mulVec (fun _ ↦ (1 : ℝ))) = 1 / 2 →
      dotProduct b (fun i ↦ (A.mulVec (fun _ ↦ (1 : ℝ)) i) ^ 2) = 1 / 3 →
      dotProduct b ((A * A).mulVec (fun _ ↦ (1 : ℝ))) = 1 / 6 →
      absoluteMonotonicityRadius A b =
        ENNReal.ofReal ((s : ℝ) - 1 + Real.sqrt ((s : ℝ) ^ 2 - 1)) →
      ∃ e : Fin s ≃ Fin s,
        A.submatrix e e = sdirkA s ∧ (fun j ↦ b (e j)) = sdirkB s) := by
  exact ⟨third_order_optimal_radius hs, sdirk_order_one (by omega),
    sdirk_order_two (by omega), sdirk_order_three_node hs,
    by simpa only [Matrix.mulVec_mulVec, ones] using sdirk_order_three_tree hs,
    sdirk_radius hs, fun A b hord1 hord2 _ hord3 hradius ↦
      third_order_unique_of_radius_eq hs A b hord1 hord2 hord3 hradius⟩

end SSPRK.Paper
