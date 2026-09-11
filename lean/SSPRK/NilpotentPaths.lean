import SSPRK.RKTransform
import Mathlib.Tactic

/-!
# Positive paths in nonnegative nilpotent matrices

This module records the local matrix facts used to turn a nilpotent nonnegative matrix into an
acyclic directed support graph.
-/

open scoped BigOperators

namespace SSPRK

noncomputable section

/-- The directed support relation of a real matrix. -/
def PositiveEdge {s : ℕ} (P : Matrix (Fin s) (Fin s) ℝ) (i j : Fin s) : Prop :=
  0 < P i j

lemma matrix_pow_nonneg {s : ℕ} (P : Matrix (Fin s) (Fin s) ℝ)
    (hP : MatrixNonneg P) (n : ℕ) : MatrixNonneg (P ^ n) := by
  induction n with
  | zero =>
      intro i j
      simp [Matrix.one_apply, ite_nonneg]
  | succ n ih =>
      rw [pow_succ]
      intro i j
      simp only [Matrix.mul_apply]
      exact Finset.sum_nonneg fun k _ ↦ mul_nonneg (ih i k) (hP k j)

/-- A positive entry of a product has a positive intermediate factor when every summand is
nonnegative. -/
lemma exists_positive_factor_of_mul_apply_pos {s : ℕ} (Q P : Matrix (Fin s) (Fin s) ℝ)
    (hQ : MatrixNonneg Q) (hP : MatrixNonneg P) {i j : Fin s} (h : 0 < (Q * P) i j) :
    ∃ k, 0 < Q i k ∧ 0 < P k j := by
  rw [Matrix.mul_apply] at h
  by_contra! hnone
  have hterm (k : Fin s) : Q i k * P k j ≤ 0 := by
    by_cases hq : 0 < Q i k
    · exact mul_nonpos_of_nonneg_of_nonpos (hQ i k) (hnone k hq)
    · exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hq) (hP k j)
  have : ∑ k, Q i k * P k j ≤ 0 := Finset.sum_nonpos fun k _ ↦ hterm k
  linarith

/-- Every positive power entry can be extended backwards by one positive support edge. -/
lemma exists_positive_power_factor {s : ℕ} (P : Matrix (Fin s) (Fin s) ℝ)
    (hP : MatrixNonneg P) {n : ℕ} {i j : Fin s} (h : 0 < (P ^ (n + 1)) i j) :
    ∃ k, 0 < (P ^ n) i k ∧ PositiveEdge P k j := by
  rw [pow_succ] at h
  obtain ⟨k, hk, hkj⟩ := exists_positive_factor_of_mul_apply_pos (P ^ n) P
    (matrix_pow_nonneg P hP n) hP h
  exact ⟨k, hk, hkj⟩

/-- A positive self-edge survives in every positive power of a nonnegative matrix. -/
lemma pow_diag_pos_of_edge {s : ℕ} (P : Matrix (Fin s) (Fin s) ℝ)
    (hP : MatrixNonneg P) {i : Fin s} (hii : PositiveEdge P i i) :
    ∀ n : ℕ, 0 < (P ^ (n + 1)) i i := by
  intro n
  induction n with
  | zero => simpa [PositiveEdge] using hii
  | succ n ih =>
      rw [pow_succ]
      have hterm : 0 < (P ^ (n + 1)) i i * P i i := mul_pos ih hii
      calc
        0 < (P ^ (n + 1)) i i * P i i := hterm
        _ ≤ ∑ k, (P ^ (n + 1)) i k * P k i :=
          Finset.single_le_sum (fun k _ ↦ mul_nonneg (matrix_pow_nonneg P hP (n + 1) i k)
            (hP k i)) (Finset.mem_univ i)

/-- A nonnegative matrix with `P ^ s = 0` has no positive self-edge when `s > 0`. -/
theorem no_positive_self_edge_of_pow_eq_zero {s : ℕ} (P : Matrix (Fin s) (Fin s) ℝ)
    (hP : MatrixNonneg P) (hnil : P ^ s = 0) {i : Fin s} : ¬PositiveEdge P i i := by
  intro hii
  cases s with
  | zero => exact Fin.elim0 i
  | succ n =>
      have hpos := pow_diag_pos_of_edge P hP hii n
      rw [hnil] at hpos
      simp at hpos

end

end SSPRK
