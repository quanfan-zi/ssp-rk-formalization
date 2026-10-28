import SSPRK.RKAllMoments

/-!
# Proposition 3.2: the all-order RK--PH moment dictionary

Both conclusions refer to the normalized positive-time PH law, so the factor
`rkSigma` remains in the denominator. The second conclusion uses only the chain
conditions, not the additional branching order conditions of a nonlinear RK method.
-/

open MeasureTheory
open scoped BigOperators

namespace SSPRK.Paper

/-- Proposition 3.2: all positive moments, and their values under chain order conditions. -/
theorem proposition_3_2 {s : ℕ} (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ)
    (r : ℝ) (hr : 0 < r) (h : AbsolutelyMonotoneAt A b r)
    (hord1 : dotProduct b (fun _ ↦ (1 : ℝ)) = 1) :
    (∀ j : ℕ, 1 ≤ j →
      (∫ x, x ^ j ∂(h.normalizedPhaseType hr hord1).measure) =
        (j.factorial : ℝ) *
          dotProduct ((rkSigma r b A)⁻¹ • rkOmega r b A)
            ((rkN r A ^ j).mulVec (fun _ ↦ 1)) ∧
      (∫ x, x ^ j ∂(h.normalizedPhaseType hr hord1).measure) =
        (j.factorial : ℝ) * r / rkSigma r b A *
          dotProduct b ((rkN r A ^ (j - 1)).mulVec (fun _ ↦ 1))) ∧
    (∀ p : ℕ,
      (∀ k : ℕ, k < p → dotProduct b ((A ^ k).mulVec (fun _ ↦ (1 : ℝ))) =
        1 / ((k + 1).factorial : ℝ)) →
      ∀ j : ℕ, 1 ≤ j → j ≤ p →
        (∫ x, x ^ j ∂(h.normalizedPhaseType hr hord1).measure) =
          (j.factorial : ℝ) * r / rkSigma r b A *
            ∑ k ∈ Finset.range j, ((j - 1).choose k : ℝ) * r ^ k /
              ((k + 1).factorial : ℝ)) := by
  constructor
  · intro j hj
    refine ⟨?_, h.normalizedPhaseType_integral_pow hr hord1 j hj⟩
    simpa only [h.normalizedPhaseType_initial hr hord1,
      h.normalizedPhaseType_green hr hord1, h.normalizedPhaseType_rate hr hord1,
      one_pow, div_one] using (h.normalizedPhaseType hr hord1).integral_pow_measure j hj
  · intro p hchain j hj hjp
    rw [h.normalizedPhaseType_integral_pow hr hord1 j hj, rkN_pow_weighted_binomial]
    refine congrArg (fun t : ℝ ↦ (j.factorial : ℝ) * r / rkSigma r b A * t)
      (Finset.sum_congr (congrArg Finset.range (Nat.sub_add_cancel hj)) ?_)
    exact fun k hk ↦ by
      simp [hchain k (lt_of_lt_of_le (Finset.mem_range.mp hk) hjp), div_eq_mul_inv]

end SSPRK.Paper
