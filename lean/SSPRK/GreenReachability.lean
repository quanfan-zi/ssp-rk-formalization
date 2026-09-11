import SSPRK.Substochastic

/-!
# Positivity and reachability for Green matrices

The identity `N * (1 - P) = 1` rewrites as `N = 1 + N * P`. For nonnegative
matrices this gives lower bounds on the diagonal and row sums, and propagates
strict positivity along one positive transition of `P`.
-/

open scoped BigOperators

namespace SSPRK

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The right Green identity in its additive form. -/
theorem green_eq_one_add_mul {P N : Matrix ι ι ℝ} (hright : N * (1 - P) = 1) :
    N = 1 + N * P := by
  rw [← hright]
  noncomm_ring

/-- Every diagonal entry of a nonnegative Green matrix is at least one. -/
theorem one_le_green_diag_of_mul_one_sub {P N : Matrix ι ι ℝ}
    (hP : ∀ i j, 0 ≤ P i j) (hN : ∀ i j, 0 ≤ N i j)
    (hright : N * (1 - P) = 1) (i : ι) :
    1 ≤ N i i := by
  rw [green_eq_one_add_mul hright, Matrix.add_apply, Matrix.one_apply, if_pos rfl]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun j _ ↦ mul_nonneg (hN i j) (hP j i))

/-- Every row sum of a nonnegative Green matrix is at least one. -/
theorem one_le_green_mulVec_one_of_mul_one_sub {P N : Matrix ι ι ℝ}
    (hP : ∀ i j, 0 ≤ P i j) (hN : ∀ i j, 0 ≤ N i j)
    (hright : N * (1 - P) = 1) (i : ι) :
    1 ≤ Matrix.mulVec N (1 : ι → ℝ) i := by
  calc
    1 ≤ N i i := one_le_green_diag_of_mul_one_sub hP hN hright i
    _ ≤ Matrix.mulVec N (1 : ι → ℝ) i := by
      simp only [Matrix.mulVec, dotProduct, Pi.one_apply, mul_one]
      exact Finset.single_le_sum (fun j _ ↦ hN i j) (Finset.mem_univ i)

/-- Green positivity propagates across one positive transition of `P`. -/
theorem green_pos_of_pos_of_mul_one_sub {P N : Matrix ι ι ℝ}
    (hP : ∀ i j, 0 ≤ P i j) (hN : ∀ i j, 0 ≤ N i j)
    (hright : N * (1 - P) = 1) {i j k : ι}
    (hNij : 0 < N i j) (hPjk : 0 < P j k) :
    0 < N i k := by
  have hterm : 0 < N i j * P j k := mul_pos hNij hPjk
  have hle : N i j * P j k ≤ (N * P) i k := by
    rw [Matrix.mul_apply]
    exact Finset.single_le_sum
      (fun l _ ↦ mul_nonneg (hN i l) (hP l k)) (Finset.mem_univ j)
  have hprod : 0 < (N * P) i k := hterm.trans_le hle
  rw [green_eq_one_add_mul hright, Matrix.add_apply, Matrix.one_apply]
  exact add_pos_of_nonneg_of_pos (by positivity) hprod

namespace Substochastic

/-- Every diagonal entry of a nonsingular substochastic Green matrix is at least one. -/
theorem one_le_inv_diag {P : Matrix ι ι ℝ} (hP : Substochastic P)
    (hinv : (1 - P).det ≠ 0) (i : ι) :
    1 ≤ ((1 - P)⁻¹) i i := by
  exact one_le_green_diag_of_mul_one_sub hP.nonneg (hP.inv_nonneg hinv)
    (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hinv)) i

/-- Every row sum of a nonsingular substochastic Green matrix is at least one. -/
theorem one_le_inv_mulVec_one {P : Matrix ι ι ℝ} (hP : Substochastic P)
    (hinv : (1 - P).det ≠ 0) (i : ι) :
    1 ≤ Matrix.mulVec ((1 - P)⁻¹) (1 : ι → ℝ) i := by
  exact one_le_green_mulVec_one_of_mul_one_sub hP.nonneg (hP.inv_nonneg hinv)
    (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hinv)) i

/-- A positive Green entry stays positive after one positive transition. -/
theorem inv_pos_of_pos_of_pos {P : Matrix ι ι ℝ} (hP : Substochastic P)
    (hinv : (1 - P).det ≠ 0) {i j k : ι}
    (hNij : 0 < ((1 - P)⁻¹) i j) (hPjk : 0 < P j k) :
    0 < ((1 - P)⁻¹) i k := by
  exact green_pos_of_pos_of_mul_one_sub hP.nonneg (hP.inv_nonneg hinv)
    (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hinv)) hNij hPjk

end Substochastic
end SSPRK
