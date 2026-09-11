import SSPRK.PhaseVariance
import SSPRK.VariancePotential

/-!
# The phase-count second-moment bound

The matrix form of V1.6 Theorem 3.1, including a subprobability initial row.
All potential inequalities are proved from the number of states, rather than assumed.
-/

open scoped BigOperators

namespace SSPRK

/-- The first two Green-matrix moments satisfy the phase-count minimum-variance bound. -/
theorem phase_second_moment_bound (s : ℕ) (hs : 0 < s)
    (P N : Matrix (Fin s) (Fin s) ℝ) (ω : Fin s → ℝ)
    (hP : Substochastic P) (hN : ∀ i j, 0 ≤ N i j)
    (hleft : (1 - P) * N = 1) (hright : N * (1 - P) = 1)
    (hω : ∀ i, 0 ≤ ω i) (hmass : ∑ i, ω i ≤ 1) :
    ((s : ℝ) + 1) * (dotProduct ω (N.mulVec (fun _ ↦ (1 : ℝ)))) ^ 2 ≤
      2 * (s : ℝ) * dotProduct ω (N.mulVec (N.mulVec (fun _ ↦ (1 : ℝ)))) := by
  have hm : ∀ i, 0 ≤ N.mulVec (fun _ ↦ (1 : ℝ)) i := by
    intro i
    change 0 ≤ ∑ j, N i j * 1
    exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (hN i j) zero_le_one
  obtain ⟨f, _, hlower, hupper, hdiff⟩ := exists_variance_potential s _ hm
  have hk : (0 : ℝ) ≤ s := (Nat.cast_pos.mpr hs).le
  exact phase_second_moment_bound_of_potential P N ω f s hP hN hk hleft hright
    hω hmass hlower hupper hdiff

end SSPRK
