import SSPRK.RKTransform
import SSPRK.Substochastic

/-!
# Substochastic bridge for the Runge--Kutta transform

This module turns the four absolute-monotonicity inequalities into a
substochastic transformed matrix and recovers nonnegativity of $N$ from its
Green-matrix representation.
-/

open scoped BigOperators

namespace SSPRK

noncomputable section

theorem rkP_substochastic {s : ℕ} (r : ℝ) (A : Matrix (Fin s) (Fin s) ℝ)
    (hinv : (rkN r A).det ≠ 0)
    (ham1 : 0 ≤ Matrix.mulVec (rkM r A) (ones s))
    (ham2 : MatrixNonneg (r • (A * rkM r A))) :
    Substochastic (rkP r A) := by
  constructor
  · exact rkP_nonneg r A hinv ham2
  · intro i
    have hrow := (rkP_mulVec_ones_le_ones r A ham1) i
    simpa [Matrix.mulVec, dotProduct, ones] using hrow

theorem one_sub_rkP_eq_rkM {s : ℕ} (r : ℝ) (A : Matrix (Fin s) (Fin s) ℝ) :
    1 - rkP r A = rkM r A := by
  rw [rkP]
  noncomm_ring

theorem one_sub_rkP_det_ne_zero {s : ℕ} (r : ℝ) (A : Matrix (Fin s) (Fin s) ℝ)
    (hinv : (rkN r A).det ≠ 0) :
    (1 - rkP r A).det ≠ 0 := by
  rw [one_sub_rkP_eq_rkM]
  intro hM
  have hNM := congrArg Matrix.det (rkN_mul_rkM r A hinv)
  simp [Matrix.det_mul, hM] at hNM

theorem rkN_eq_inv_one_sub_rkP {s : ℕ} (r : ℝ) (A : Matrix (Fin s) (Fin s) ℝ)
    (hinv : (rkN r A).det ≠ 0) :
    rkN r A = (1 - rkP r A)⁻¹ := by
  rw [one_sub_rkP_eq_rkM, rkM]
  exact (Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hinv)).symm

theorem rkN_nonneg {s : ℕ} (r : ℝ) (A : Matrix (Fin s) (Fin s) ℝ)
    (hinv : (rkN r A).det ≠ 0) (hP : Substochastic (rkP r A)) :
    MatrixNonneg (rkN r A) := by
  intro i j
  rw [rkN_eq_inv_one_sub_rkP r A hinv]
  exact hP.inv_nonneg (one_sub_rkP_det_ne_zero r A hinv) i j

end

end SSPRK
