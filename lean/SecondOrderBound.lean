import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Linarith
import SSPRK.PhaseMomentBound
import SSPRK.RKSubstochastic

/-!
# The second-order SSP bound from explicit matrix constraints

The upper-bound part of Theorem 5.2: every real tableau satisfying the two
second-order conditions and the four complete SSP inequalities has `r ≤ 2 * s`.

The proof uses the transform of Section 2.4, the finite Green-matrix form of the
minimum-variance bound in Theorem 3.1, and the moment identities (2.26). It retains
the subprobability weights directly, without dividing by their total mass.
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
  -- Section 2.4: the SSP constraints give a substochastic transform,
  -- a nonnegative Green matrix, and nonnegative initial weights of mass at most one.
  have hP : Substochastic (rkP r A) := rkP_substochastic r A hinv ham1 ham2
  have hN : MatrixNonneg (rkN r A) := rkN_nonneg r A hinv hP
  have hω : 0 ≤ rkOmega r b A := rkOmega_nonneg r b A hr.le ham3
  have hmass : ∑ i, rkOmega r b A i ≤ 1 := by
    simpa [rkSigma, ones, dotProduct] using rkSigma_le_one r b A ham4
  have hleft : (1 - rkP r A) * rkN r A = 1 := by
    rw [one_sub_rkP_eq_rkM]
    exact rkM_mul_rkN r A hinv
  have hright : rkN r A * (1 - rkP r A) = 1 := by
    rw [one_sub_rkP_eq_rkM]
    exact rkN_mul_rkM r A hinv
  -- Apply the finite-matrix version of Theorem 3.1 to these data.
  have hbound := phase_second_moment_bound s hs (rkP r A) (rkN r A)
    (rkOmega r b A) hP hN hleft hright hω hmass
  -- Equation (2.26): the two order conditions evaluate the weighted matrix moments.
  have hfirst : dotProduct (rkOmega r b A) ((rkN r A).mulVec (ones s)) = r := by
    rw [Matrix.dotProduct_mulVec]
    exact rkOmega_N_ones_eq r b A hinv hord1
  have hsecond : dotProduct (rkOmega r b A)
      ((rkN r A).mulVec ((rkN r A).mulVec (ones s))) = r + r ^ 2 / 2 := by
    rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    exact rkOmega_N_sq_ones_eq r b A hinv hord1 hord2
  change ((s : ℝ) + 1) *
    (dotProduct (rkOmega r b A) ((rkN r A).mulVec (ones s))) ^ 2 ≤
      2 * (s : ℝ) * dotProduct (rkOmega r b A)
        ((rkN r A).mulVec ((rkN r A).mulVec (ones s))) at hbound
  -- Substitute the moments into hbound; the remaining inequality is purely scalar.
  rw [hfirst, hsecond] at hbound
  exact second_order_bound_of_weighted_moment_inequality s r hr hbound

end SSPRK
