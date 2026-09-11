import SSPRK.RKTransform
import Mathlib.Data.ENNReal.Real

/-!
# Complete absolute-monotonicity constraints and radius

The algebraic feasible set and its extended nonnegative supremum, as in V1.6,
Section 2.4. Order conditions are imposed separately by the application theorems.
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

end SSPRK
