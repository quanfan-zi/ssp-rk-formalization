import SSPRK.PhaseTypeThirdDefect
import SSPRK.RKThirdMoment

/-!
# The third-order SSP bound from explicit matrix constraints

The upper-bound part of V2.10 Theorem 5.2: the three chain order conditions and the four
complete SSP inequalities give the sharp bound at every positive feasible parameter.
The additional third-order condition on squared nodes is not needed for this bound.

The proof uses the RK--PH construction and moments of V2.10, Propositions 3.1--3.2,
and the defect proof of Theorem 4.2. Here the integral moments include a possible
atom at zero, so they are the unnormalized counterparts of the paper's moments.
-/

open scoped BigOperators

namespace SSPRK

/-- Substitute the RK moments into the PH bound and cancel the positive squared mean. -/
theorem third_order_quadratic_of_moment_bound {s r : ℝ} (hr : 0 < r)
    (hbound : (s + 2) * (r ^ 2 + 2 * r) ^ 2 ≤
      (s + 1) * r * (r ^ 3 + 6 * r ^ 2 + 6 * r)) :
    r ^ 2 - 2 * (s - 1) * r - 2 * (s - 1) ≤ 0 := by
  apply nonpos_of_mul_nonpos_left (b := r ^ 2) _ (sq_pos_of_pos hr)
  nlinarith only [hbound]

/-- The positive root of the RK moment quadratic gives the third-order radius bound. -/
theorem third_order_bound_of_quadratic {s r : ℝ} (hs : 1 ≤ s)
    (hquad : r ^ 2 - 2 * (s - 1) * r - 2 * (s - 1) ≤ 0) :
    r ≤ s - 1 + Real.sqrt (s ^ 2 - 1) := by
  have hdisc : 0 ≤ s ^ 2 - 1 := by nlinarith only [hs]
  have hroot := Real.sq_sqrt hdisc
  have hnonneg := Real.sqrt_nonneg (s ^ 2 - 1)
  by_contra! h
  nlinarith only [hquad, hroot, hnonneg, h]

/-- V2.10 Theorem 5.2: the bound at every positive feasible parameter,
with invertibility, chain order conditions, and all four SSP constraints explicit. -/
theorem third_order_rk_ssp_bound
    (s : ℕ)
    (hs : 2 ≤ s)
    (A : Matrix (Fin s) (Fin s) ℝ)
    (b : Fin s → ℝ)
    (r : ℝ)
    (hr : 0 < r)
    (hinv : (1 + r • A).det ≠ 0)
    -- Chain order conditions.
    (hord1 :
      dotProduct b (fun _ ↦ (1 : ℝ)) = 1)
    (hord2 :
      dotProduct b (Matrix.mulVec A (fun _ ↦ (1 : ℝ))) = 1 / 2)
    (hord3 :
      dotProduct b ((A * A).mulVec (fun _ ↦ (1 : ℝ))) = 1 / 6)
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
    r ≤ (s : ℝ) - 1 + Real.sqrt ((s : ℝ) ^ 2 - 1) := by
  -- V2.10, Proposition 3.1: package the explicit constraints to construct the PH probability law.
  let h : AbsolutelyMonotoneAt A b r := ⟨hinv, ham1, ham2, ham3, ham4⟩
  -- Unnormalized counterpart of V2.10, Proposition 3.2: evaluate the three integral moments,
  -- including zero mass.
  have hfirst : ∫ x, x ∂(h.phaseType hr).measure = r :=
    h.phaseType_integral_id hr hord1
  have hsecond : ∫ x, x ^ 2 ∂(h.phaseType hr).measure = r ^ 2 + 2 * r :=
    h.phaseType_integral_sq hr hord1 hord2
  have hthird : ∫ x, x ^ 3 ∂(h.phaseType hr).measure = r ^ 3 + 6 * r ^ 2 + 6 * r :=
    h.phaseType_integral_cube hr hord1 hord2 hord3
  have hmean : 0 < ∫ x, x ∂(h.phaseType hr).measure := by
    rw [hfirst]
    exact hr
  -- Apply the defect bound underlying V2.10, Theorem 4.2, and substitute the evaluated moments into
  -- its inequality.
  have hbound := (h.phaseType hr).third_moment_lower_bound_defect hmean
  rw [hfirst, hsecond, hthird] at hbound
  -- V2.10, Section 5.2: reduce to a quadratic inequality and select its upper root.
  apply third_order_bound_of_quadratic (by exact_mod_cast (show 1 ≤ s by omega))
  exact third_order_quadratic_of_moment_bound hr hbound

end SSPRK
