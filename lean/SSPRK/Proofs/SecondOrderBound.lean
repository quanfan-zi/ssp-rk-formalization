import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Linarith
import SSPRK.PaperSecondOrderBound

/-!
# The second-order SSP bound from explicit matrix constraints

The upper-bound part of Theorem 5.2: every real tableau satisfying the two
second-order conditions and the four complete SSP inequalities has `r ≤ 2 * s`.

The V2.10 proof uses the normalized RK--PH transform and the existing
minimum-variance theorem. It retains the conditional estimate with the factor
`rkSigma` before using the upper bound of one on that initial mass.
-/

open scoped BigOperators

namespace SSPRK

/-- The denominator-free final step for the subprobability moment bound. -/
lemma second_order_bound_of_weighted_moment_inequality
    (s r : ℝ) (hr : 0 < r)
    (hbound : (s + 1) * r ^ 2 ≤ 2 * s * (r + r ^ 2 / 2)) : r ≤ 2 * s := by
  nlinarith

/-- Theorem 5.2: the bound at every positive feasible parameter,
with invertibility, order conditions, and all four SSP constraints stated explicitly. -/
theorem second_order_rk_ssp_bound
    (s : ℕ)
    (hs : 0 < s)
    (A : Matrix (Fin s) (Fin s) ℝ)
    (b : Fin s → ℝ)
    (r : ℝ)
    (hr : 0 < r)
    (hinv : (1 + r • A).det ≠ 0)
    -- Second-order conditions.
    (hord1 :
      dotProduct b (fun _ ↦ (1 : ℝ)) = 1)
    (hord2 :
      dotProduct b (Matrix.mulVec A (fun _ ↦ (1 : ℝ))) = 1 / 2)
    -- Four absolute-monotonicity conditions.
    (ham1 :
      0 ≤ Matrix.mulVec ((1 + r • A)⁻¹) (fun _ ↦ (1 : ℝ)))
    (ham2 :
      ∀ i j : Fin s, 0 ≤ (r • (A * (1 + r • A)⁻¹)) i j)
    (ham3 :
      0 ≤ Matrix.vecMul b ((1 + r • A)⁻¹))
    (ham4 :
      0 ≤ 1 - r * dotProduct
        (Matrix.vecMul b ((1 + r • A)⁻¹)) (fun _ ↦ (1 : ℝ))) :
    r ≤ 2 * (s : ℝ) := by
  let h : AbsolutelyMonotoneAt A b r := ⟨hinv, ham1, ham2, ham3, ham4⟩
  exact h.second_order_bound_normalized hr hs hord1 hord2

end SSPRK
