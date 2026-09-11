import SSPRK.MidpointAttainment

/-!
# The optimal second-order radius

The numerical equality in V1.6 Theorem 5.2: the supremum over all real second-order
tableaux with `s` stages equals `2s`. Classification of all optimizers is a separate result.
-/

open scoped ENNReal

namespace SSPRK

/-- Complete radii of all real tableaux satisfying the two second-order conditions. -/
def secondOrderTableauRadii (s : ℕ) : Set ℝ≥0∞ :=
  {ρ | ∃ (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ),
    dotProduct b (fun _ ↦ (1 : ℝ)) = 1 ∧
    dotProduct b (A.mulVec (fun _ ↦ (1 : ℝ))) = 1 / 2 ∧
    absoluteMonotonicityRadius A b = ρ}

/-- The optimal complete radius over all second-order `s`-stage tableaux. -/
noncomputable def secondOrderOptimalRadius (s : ℕ) : ℝ≥0∞ :=
  sSup (secondOrderTableauRadii s)

/-- General implicit methods attain the optimal second-order SSP radius `2s`. -/
theorem second_order_optimal_radius {s : ℕ} (hs : 0 < s) :
    secondOrderOptimalRadius s = ENNReal.ofReal (2 * (s : ℝ)) := by
  apply le_antisymm
  · apply sSup_le
    rintro ρ ⟨A, b, hord1, hord2, rfl⟩
    exact second_order_radius_bound hs A b hord1 hord2
  · apply le_sSup
    exact ⟨midpointA s, midpointB s, midpoint_order_one hs, midpoint_order_two hs,
      midpoint_radius hs⟩

end SSPRK
