import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Runge--Kutta absolute-monotonicity transform

Reusable definitions and algebraic identities for the transform used in the
SSP Runge--Kutta bounds.
-/

open scoped BigOperators

namespace SSPRK

noncomputable section

/-- The vector whose entries are all one. -/
def ones (s : ℕ) : Fin s → ℝ := fun _ ↦ 1

/-- Entrywise nonnegativity of a real matrix. -/
def MatrixNonneg {s : ℕ} (A : Matrix (Fin s) (Fin s) ℝ) : Prop :=
  ∀ i j, 0 ≤ A i j

/-- The shifted Runge--Kutta matrix $N = I + r A$. -/
def rkN {s : ℕ} (r : ℝ) (A : Matrix (Fin s) (Fin s) ℝ) : Matrix (Fin s) (Fin s) ℝ :=
  1 + r • A

/-- The nonsingular inverse $M = N^{-1}$. -/
def rkM {s : ℕ} (r : ℝ) (A : Matrix (Fin s) (Fin s) ℝ) : Matrix (Fin s) (Fin s) ℝ :=
  (rkN r A)⁻¹

/-- The transformed matrix $P = I - M$. -/
def rkP {s : ℕ} (r : ℝ) (A : Matrix (Fin s) (Fin s) ℝ) : Matrix (Fin s) (Fin s) ℝ :=
  1 - rkM r A

/-- The transformed output weights $ω = r b M$. -/
def rkOmega {s : ℕ} (r : ℝ) (b : Fin s → ℝ) (A : Matrix (Fin s) (Fin s) ℝ) : Fin s → ℝ :=
  r • Matrix.vecMul b (rkM r A)

/-- The scalar $σ = ω e$. -/
def rkSigma {s : ℕ} (r : ℝ) (b : Fin s → ℝ) (A : Matrix (Fin s) (Fin s) ℝ) : ℝ :=
  dotProduct (rkOmega r b A) (ones s)

theorem rkN_mul_rkM {s : ℕ} (r : ℝ) (A : Matrix (Fin s) (Fin s) ℝ)
    (hinv : (rkN r A).det ≠ 0) :
    rkN r A * rkM r A = 1 := by
  unfold rkM
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hinv)

theorem rkM_mul_rkN {s : ℕ} (r : ℝ) (A : Matrix (Fin s) (Fin s) ℝ)
    (hinv : (rkN r A).det ≠ 0) :
    rkM r A * rkN r A = 1 := by
  unfold rkM
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hinv)

theorem rkP_eq_r_smul_mul {s : ℕ} (r : ℝ) (A : Matrix (Fin s) (Fin s) ℝ)
    (hinv : (rkN r A).det ≠ 0) :
    rkP r A = r • (A * rkM r A) := by
  rw [rkP, ← rkN_mul_rkM r A hinv, rkN]
  noncomm_ring

theorem rkOmega_vecMul_rkN {s : ℕ} (r : ℝ) (b : Fin s → ℝ)
    (A : Matrix (Fin s) (Fin s) ℝ) (hinv : (rkN r A).det ≠ 0) :
    Matrix.vecMul (rkOmega r b A) (rkN r A) = r • b := by
  rw [rkOmega, Matrix.smul_vecMul, Matrix.vecMul_vecMul, rkM_mul_rkN r A hinv]
  simp

theorem rkP_nonneg {s : ℕ} (r : ℝ) (A : Matrix (Fin s) (Fin s) ℝ)
    (hinv : (rkN r A).det ≠ 0) (hP : MatrixNonneg (r • (A * rkM r A))) :
    MatrixNonneg (rkP r A) := by
  rw [rkP_eq_r_smul_mul r A hinv]
  exact hP

theorem rkP_mulVec_ones_le_ones {s : ℕ} (r : ℝ) (A : Matrix (Fin s) (Fin s) ℝ)
    (hM : 0 ≤ Matrix.mulVec (rkM r A) (ones s)) :
    Matrix.mulVec (rkP r A) (ones s) ≤ ones s := by
  rw [rkP, Matrix.sub_mulVec, Matrix.one_mulVec]
  exact sub_le_self _ hM

theorem rkOmega_nonneg {s : ℕ} (r : ℝ) (b : Fin s → ℝ) (A : Matrix (Fin s) (Fin s) ℝ)
    (hr : 0 ≤ r) (hOmega : 0 ≤ Matrix.vecMul b (rkM r A)) :
    0 ≤ rkOmega r b A := by
  rw [rkOmega]
  exact smul_nonneg hr hOmega

theorem rkSigma_eq {s : ℕ} (r : ℝ) (b : Fin s → ℝ) (A : Matrix (Fin s) (Fin s) ℝ) :
    rkSigma r b A = r * dotProduct (Matrix.vecMul b (rkM r A)) (ones s) := by
  simp [rkSigma, rkOmega]

theorem rkSigma_nonneg {s : ℕ} (r : ℝ) (b : Fin s → ℝ) (A : Matrix (Fin s) (Fin s) ℝ)
    (hOmega : 0 ≤ rkOmega r b A) :
    0 ≤ rkSigma r b A := by
  apply dotProduct_nonneg_of_nonneg hOmega
  intro i
  simp [ones]

theorem rkSigma_le_one {s : ℕ} (r : ℝ) (b : Fin s → ℝ) (A : Matrix (Fin s) (Fin s) ℝ)
    (hbound : 0 ≤ 1 - r * dotProduct (Matrix.vecMul b (rkM r A)) (ones s)) :
    rkSigma r b A ≤ 1 := by
  rw [rkSigma_eq]
  linarith

theorem rkOmega_N_ones_eq {s : ℕ} (r : ℝ) (b : Fin s → ℝ)
    (A : Matrix (Fin s) (Fin s) ℝ) (hinv : (rkN r A).det ≠ 0)
    (hord1 : dotProduct b (ones s) = 1) :
    dotProduct (Matrix.vecMul (rkOmega r b A) (rkN r A)) (ones s) = r := by
  rw [rkOmega_vecMul_rkN r b A hinv, smul_dotProduct, hord1, smul_eq_mul, mul_one]

theorem rkSigma_pos {s : ℕ} (r : ℝ) (b : Fin s → ℝ) (A : Matrix (Fin s) (Fin s) ℝ)
    (hr : 0 < r) (hOmega : 0 ≤ rkOmega r b A)
    (hmoment : dotProduct (Matrix.vecMul (rkOmega r b A) (rkN r A)) (ones s) = r) :
    0 < rkSigma r b A := by
  have hnonneg : 0 ≤ rkSigma r b A := rkSigma_nonneg r b A hOmega
  refine lt_of_le_of_ne hnonneg ?_
  intro hzero
  have hsum : ∑ i, rkOmega r b A i = 0 := by
    simpa [rkSigma, dotProduct, ones] using hzero.symm
  have hOmega_zero : rkOmega r b A = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg fun i ↦ hOmega i).mp hsum
  have hmoment_zero : dotProduct (Matrix.vecMul (rkOmega r b A) (rkN r A)) (ones s) = 0 := by
    simp [hOmega_zero]
  linarith

theorem rkN_mulVec_ones {s : ℕ} (r : ℝ) (A : Matrix (Fin s) (Fin s) ℝ) :
    Matrix.mulVec (rkN r A) (ones s) = ones s + r • Matrix.mulVec A (ones s) := by
  rw [rkN, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]

theorem rkN_sq_eq {s : ℕ} (r : ℝ) (A : Matrix (Fin s) (Fin s) ℝ) :
    rkN r A * rkN r A = 1 + (2 * r) • A + r ^ 2 • (A * A) := by
  rw [rkN]
  noncomm_ring
  simp [smul_add, smul_smul]
  conv_lhs => rw [← add_assoc, ← add_smul]
  rw [two_mul]

theorem rkN_sq_mulVec_ones {s : ℕ} (r : ℝ) (A : Matrix (Fin s) (Fin s) ℝ) :
    Matrix.mulVec (rkN r A * rkN r A) (ones s) =
      ones s + (2 * r) • Matrix.mulVec A (ones s) + r ^ 2 • Matrix.mulVec (A * A) (ones s) := by
  rw [rkN_sq_eq, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec]

theorem rkOmega_N_sq_ones_eq {s : ℕ} (r : ℝ) (b : Fin s → ℝ)
    (A : Matrix (Fin s) (Fin s) ℝ) (hinv : (rkN r A).det ≠ 0)
    (hord1 : dotProduct b (ones s) = 1)
    (hord2 : dotProduct b (Matrix.mulVec A (ones s)) = 1 / 2) :
    dotProduct (Matrix.vecMul (rkOmega r b A) (rkN r A * rkN r A)) (ones s) =
      r + r ^ 2 / 2 := by
  rw [← Matrix.vecMul_vecMul, rkOmega_vecMul_rkN r b A hinv, ← Matrix.dotProduct_mulVec,
    rkN_mulVec_ones, smul_dotProduct, dotProduct_add, dotProduct_smul, hord1, hord2]
  simp only [smul_eq_mul]
  ring

theorem rkOmega_N_cu_ones_eq {s : ℕ} (r : ℝ) (b : Fin s → ℝ)
    (A : Matrix (Fin s) (Fin s) ℝ) (hinv : (rkN r A).det ≠ 0)
    (hord1 : dotProduct b (ones s) = 1)
    (hord2 : dotProduct b (Matrix.mulVec A (ones s)) = 1 / 2)
    (hord3 : dotProduct b (Matrix.mulVec (A * A) (ones s)) = 1 / 6) :
    dotProduct
        (Matrix.vecMul (rkOmega r b A) (rkN r A * rkN r A * rkN r A)) (ones s) =
      r + r ^ 2 + r ^ 3 / 6 := by
  rw [Matrix.mul_assoc, ← Matrix.vecMul_vecMul, rkOmega_vecMul_rkN r b A hinv,
    ← Matrix.dotProduct_mulVec, rkN_sq_mulVec_ones, smul_dotProduct, dotProduct_add,
    dotProduct_add, dotProduct_smul, dotProduct_smul, hord1, hord2, hord3]
  simp only [smul_eq_mul]
  ring

end

end SSPRK
