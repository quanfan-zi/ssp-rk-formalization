import SSPRK.DownwardClosure

/-!
# The zero endpoint of absolute monotonicity

Positive absolute monotonicity already forces the tableau coefficients to be nonnegative.
Consequently the defining inequalities also hold at radius zero.
-/

open scoped BigOperators

namespace SSPRK

noncomputable section

namespace AbsolutelyMonotoneAt

variable {s : ℕ} {A : Matrix (Fin s) (Fin s) ℝ} {b : Fin s → ℝ} {r : ℝ}

theorem matrix_nonneg_of_pos (h : AbsolutelyMonotoneAt A b r) (hr : 0 < r) :
    MatrixNonneg A := by
  have hP : Substochastic (rkP r A) :=
    rkP_substochastic r A h.det_ne_zero h.stages h.matrix_nonneg
  have hN : MatrixNonneg (rkN r A) := rkN_nonneg r A h.det_ne_zero hP
  have hPN : rkP r A * rkN r A = r • A := by
    rw [rkP_eq_r_smul_mul r A h.det_ne_zero, Matrix.smul_mul, Matrix.mul_assoc,
      rkM_mul_rkN r A h.det_ne_zero]
    simp
  intro i j
  have hprod : 0 ≤ (rkP r A * rkN r A) i j := by
    simp only [Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ ↦ mul_nonneg (hP.nonneg i k) (hN k j)
  rw [hPN, Matrix.smul_apply, smul_eq_mul] at hprod
  exact nonneg_of_mul_nonneg_right hprod hr

theorem output_nonneg_of_pos (h : AbsolutelyMonotoneAt A b r) (hr : 0 < r) : 0 ≤ b := by
  have hP : Substochastic (rkP r A) :=
    rkP_substochastic r A h.det_ne_zero h.stages h.matrix_nonneg
  have hN : MatrixNonneg (rkN r A) := rkN_nonneg r A h.det_ne_zero hP
  have hω : 0 ≤ rkOmega r b A := rkOmega_nonneg r b A hr.le h.output_nonneg
  have hωN := rkOmega_vecMul_rkN r b A h.det_ne_zero
  intro j
  have hprod : 0 ≤ Matrix.vecMul (rkOmega r b A) (rkN r A) j := by
    simp only [Matrix.vecMul, dotProduct]
    exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hω i) (hN i j)
  rw [hωN, Pi.smul_apply, smul_eq_mul] at hprod
  exact nonneg_of_mul_nonneg_right hprod hr

theorem at_zero (h : AbsolutelyMonotoneAt A b r) (hr : 0 < r) :
    AbsolutelyMonotoneAt A b 0 := by
  have hA : MatrixNonneg A := h.matrix_nonneg_of_pos hr
  have hb : 0 ≤ b := h.output_nonneg_of_pos hr
  refine
    { det_ne_zero := by simp
      stages := ?_
      matrix_nonneg := ?_
      output_nonneg := ?_
      output_mass := by simp }
  · intro i
    simp
  · intro i j
    simp
  · simpa using hb

/-- Absolute monotonicity is closed on the full interval from zero to a positive radius. -/
theorem closed_downward (h : AbsolutelyMonotoneAt A b r) (hr : 0 < r)
    {theta : ℝ} (htheta0 : 0 ≤ theta) (hthetar : theta ≤ r) :
    AbsolutelyMonotoneAt A b theta := by
  rcases htheta0.eq_or_lt with rfl | htheta
  · exact h.at_zero hr
  · exact h.downward_closed htheta hthetar

end AbsolutelyMonotoneAt

end

end SSPRK
