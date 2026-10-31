import SSPRK.SecondOrderOptimality
import SSPRK.SecondOrderRadiusEquality

/-!
# V2.10, Theorem 5.1: second-order optimality and uniqueness

The canonical tableau is `midpointA s`, `midpointB s`: its diagonal is `1 / (2s)`,
its strict lower triangle is `1 / s`, its strict upper triangle is zero, and every
output weight is `1 / s`. The supremum ranges over all real tableaux satisfying
the two classical order conditions, without a triangularity assumption.

This entry assembles the existing optimality, order, attainment, and classification results.
-/

open scoped ENNReal

namespace SSPRK.Paper

/-- The complete statement of V2.10 Theorem 5.1, including attainment and classification. -/
theorem theorem_5_1 (s : ℕ) (hs : 1 ≤ s) :
    secondOrderOptimalRadius s = ENNReal.ofReal (2 * (s : ℝ)) ∧
    dotProduct (midpointB s) (fun _ ↦ (1 : ℝ)) = 1 ∧
    dotProduct (midpointB s) ((midpointA s).mulVec (fun _ ↦ (1 : ℝ))) = 1 / 2 ∧
    absoluteMonotonicityRadius (midpointA s) (midpointB s) =
      ENNReal.ofReal (2 * (s : ℝ)) ∧
    (∀ (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ),
      dotProduct b (fun _ ↦ (1 : ℝ)) = 1 →
      dotProduct b (A.mulVec (fun _ ↦ (1 : ℝ))) = 1 / 2 →
      absoluteMonotonicityRadius A b = ENNReal.ofReal (2 * (s : ℝ)) →
      ∃ e : Fin s ≃ Fin s,
        A.submatrix e e = midpointA s ∧ (fun j ↦ b (e j)) = midpointB s) := by
  exact ⟨second_order_optimal_radius hs, midpoint_order_one hs, midpoint_order_two hs,
    midpoint_radius hs, fun A b hord1 hord2 hradius ↦
      second_order_unique_of_radius_eq hs A b hord1 hord2 hradius⟩

end SSPRK.Paper
