import SSPRK.ThirdOrder
import SSPRK.SDIRKAttainment

/-!
# The optimal third-order radius

The SDIRK family satisfies all four classical order-three conditions and attains the
general upper bound. Taking the supremum over real tableaux proves the numerical optimum.
-/

open scoped ENNReal

namespace SSPRK

/-- The SDIRK family has exactly the sharp third-order complete SSP radius. -/
theorem sdirk_radius {s : ℕ} (hs : 2 ≤ s) :
    absoluteMonotonicityRadius (sdirkA s) (sdirkB s) = ENNReal.ofReal (thirdOrderRadius s) := by
  apply le_antisymm
  · apply third_order_radius_bound hs (sdirkA s) (sdirkB s)
      (sdirk_order_one (by omega)) (sdirk_order_two (by omega))
    simpa only [Matrix.mulVec_mulVec, ones] using sdirk_order_three_tree hs
  · exact (sdirk_feasible hs).le_radius (thirdOrderRadius_pos hs)

/-- Complete radii of real tableaux satisfying all classical third-order conditions. -/
def thirdOrderTableauRadii (s : ℕ) : Set ℝ≥0∞ :=
  {ρ | ∃ (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ),
    dotProduct b (fun _ ↦ (1 : ℝ)) = 1 ∧
    dotProduct b (A.mulVec (fun _ ↦ (1 : ℝ))) = 1 / 2 ∧
    dotProduct b (fun i ↦ (A.mulVec (fun _ ↦ (1 : ℝ)) i) ^ 2) = 1 / 3 ∧
    dotProduct b ((A * A).mulVec (fun _ ↦ (1 : ℝ))) = 1 / 6 ∧
    absoluteMonotonicityRadius A b = ρ}

/-- The optimal complete radius over all third-order `s`-stage real tableaux. -/
noncomputable def thirdOrderOptimalRadius (s : ℕ) : ℝ≥0∞ :=
  sSup (thirdOrderTableauRadii s)

/-- The numerical optimum in V1.6 Theorem 5.3. -/
theorem third_order_optimal_radius {s : ℕ} (hs : 2 ≤ s) :
    thirdOrderOptimalRadius s = ENNReal.ofReal (thirdOrderRadius s) := by
  apply le_antisymm
  · apply sSup_le
    rintro ρ ⟨A, b, hord1, hord2, _, hord3, rfl⟩
    exact third_order_radius_bound hs A b hord1 hord2 hord3
  · apply le_sSup
    refine ⟨sdirkA s, sdirkB s, sdirk_order_one (by omega), sdirk_order_two (by omega),
      sdirk_order_three_node hs, ?_, sdirk_radius hs⟩
    simpa only [Matrix.mulVec_mulVec, ones] using sdirk_order_three_tree hs

end SSPRK
