import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

/-!
# Finite substochastic matrices

The matrix argument in V1.6, Section 2.4: a nonnegative matrix with row sums at most one
and nonsingular `1 - P` has a nonnegative Green matrix. The proof uses bounded partial
geometric sums, avoiding an additional Perron--Frobenius dependency.
-/

open scoped BigOperators

namespace SSPRK

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Entrywise nonnegativity and row sums bounded by one. -/
structure Substochastic (P : Matrix ι ι ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ P i j
  row_sum_le : ∀ i, ∑ j, P i j ≤ 1

namespace Substochastic

theorem one : Substochastic (1 : Matrix ι ι ℝ) := by
  constructor <;> simp [Matrix.one_apply, ite_nonneg]

omit [DecidableEq ι] in
theorem mul {P Q : Matrix ι ι ℝ} (hP : Substochastic P) (hQ : Substochastic Q) :
    Substochastic (P * Q) := by
  constructor
  · intro i j
    exact Finset.sum_nonneg fun k _ ↦ mul_nonneg (hP.nonneg i k) (hQ.nonneg k j)
  · intro i
    simp_rw [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    exact (Finset.sum_le_sum fun k _ ↦
      (mul_le_mul_of_nonneg_left (hQ.row_sum_le k) (hP.nonneg i k)).trans_eq
        (mul_one _)).trans (hP.row_sum_le i)

theorem pow {P : Matrix ι ι ℝ} (hP : Substochastic P) (n : ℕ) :
    Substochastic (P ^ n) := by
  induction n with
  | zero => simpa using (one : Substochastic (1 : Matrix ι ι ℝ))
  | succ n ih => simpa [pow_succ] using ih.mul hP

omit [DecidableEq ι] in
theorem entry_le_one {P : Matrix ι ι ℝ} (hP : Substochastic P) (i j : ι) :
    P i j ≤ 1 := by
  exact (Finset.single_le_sum (fun k _ ↦ hP.nonneg i k) (Finset.mem_univ j)).trans
    (hP.row_sum_le i)

/-- A finite geometric sum expressed using the nonsingular inverse. -/
theorem sum_range_pow_eq {P : Matrix ι ι ℝ} (hinv : (1 - P).det ≠ 0) (n : ℕ) :
    ∑ k ∈ Finset.range n, P ^ k = (1 - P)⁻¹ * (1 - P ^ n) := by
  rw [← mul_neg_geom_sum P n, Matrix.nonsing_inv_mul_cancel_left _ _
    (isUnit_iff_ne_zero.mpr hinv)]

/-- Nonsingularity bounds all entrywise partial sums of the geometric series. -/
theorem sum_range_pow_entry_le {P : Matrix ι ι ℝ} (hP : Substochastic P)
    (hinv : (1 - P).det ≠ 0) (n : ℕ) (i j : ι) :
    ∑ k ∈ Finset.range n, (P ^ k) i j ≤ 2 * ∑ k, |((1 - P)⁻¹) i k| := by
  have heq := congrArg (fun Q : Matrix ι ι ℝ ↦ Q i j) (sum_range_pow_eq hinv n)
  simp only [Matrix.sum_apply, Matrix.sub_apply, Matrix.mul_apply] at heq
  rw [heq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have hentry := (hP.pow n).entry_le_one k j
  have hnonneg := (hP.pow n).nonneg k j
  have hdiff : |(1 : Matrix ι ι ℝ) k j - (P ^ n) k j| ≤ 2 := by
    rw [abs_le]
    simp only [Matrix.one_apply]
    split_ifs <;> constructor <;> linarith
  calc
    _ ≤ |((1 - P)⁻¹) i k * ((1 : Matrix ι ι ℝ) k j - (P ^ n) k j)| := le_abs_self _
    _ = |((1 - P)⁻¹) i k| * |(1 : Matrix ι ι ℝ) k j - (P ^ n) k j| := abs_mul _ _
    _ ≤ |((1 - P)⁻¹) i k| * 2 := mul_le_mul_of_nonneg_left hdiff (abs_nonneg _)
    _ = _ := mul_comm _ _

/-- The Neumann series converges, including substochastic matrices with row norm one. -/
theorem summable_pow {P : Matrix ι ι ℝ} (hP : Substochastic P)
    (hinv : (1 - P).det ≠ 0) : Summable (fun n : ℕ ↦ P ^ n) := by
  apply Pi.summable.mpr
  intro i
  apply Pi.summable.mpr
  intro j
  exact summable_of_sum_range_le (fun n ↦ (hP.pow n).nonneg i j)
    (fun n ↦ hP.sum_range_pow_entry_le hinv n i j)

/-- Equation (2.19): the Green matrix is the sum of the powers of `P`. -/
theorem inv_eq_tsum {P : Matrix ι ι ℝ} (hP : Substochastic P)
    (hinv : (1 - P).det ≠ 0) : (1 - P)⁻¹ = ∑' n : ℕ, P ^ n := by
  have h := congrArg (fun Q : Matrix ι ι ℝ ↦ (1 - P)⁻¹ * Q)
    (hP.summable_pow hinv).one_sub_mul_tsum_pow
  simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.mpr hinv),
    Matrix.mul_one] using h.symm

/-- The Green matrix of a nonsingular substochastic model is entrywise nonnegative. -/
theorem inv_nonneg {P : Matrix ι ι ℝ} (hP : Substochastic P)
    (hinv : (1 - P).det ≠ 0) : ∀ i j, 0 ≤ ((1 - P)⁻¹) i j := by
  rw [hP.inv_eq_tsum hinv]
  intro i j
  have ht := Pi.hasSum.mp (Pi.hasSum.mp (hP.summable_pow hinv).hasSum i) j
  rw [← ht.tsum_eq]
  exact tsum_nonneg (fun n ↦ (hP.pow n).nonneg i j)

end Substochastic
end SSPRK
