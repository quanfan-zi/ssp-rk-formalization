import SSPRK.GreenReachability
import SSPRK.PhaseTypeData

/-!
# Principal Green matrices for phase-type data

Removing the distinguished state `0` leaves a transient principal transition block. Its Green
matrix is the Schur residual of the original Green matrix at the positive pivot `G 0 0`.
-/

open scoped BigOperators

namespace SSPRK.PhaseTypeData

variable {n : ℕ} (d : PhaseTypeData (n + 1))

/-- The lower-right transition block obtained by deleting state `0`. -/
noncomputable def principalTransition : Matrix (Fin n) (Fin n) ℝ :=
  d.transition.submatrix Fin.succ Fin.succ

/-- The Schur residual of the full Green matrix after deleting state `0`. -/
noncomputable def principalGreenResidual : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ d.green i.succ j.succ - d.green i.succ 0 * d.green 0 j.succ / d.green 0 0

/-- The distinguished Green diagonal entry is strictly positive. -/
theorem green_zero_zero_pos : 0 < d.green 0 0 := by
  have hdiag := d.substochastic.one_le_inv_diag d.transient 0
  exact lt_of_lt_of_le zero_lt_one (by simpa only [green] using hdiag)

/-- Deleting state `0` preserves substochasticity. -/
theorem principalTransition_substochastic : Substochastic d.principalTransition := by
  constructor
  · intro i j
    exact d.substochastic.nonneg i.succ j.succ
  · intro i
    have hrow := d.substochastic.row_sum_le i.succ
    rw [Fin.sum_univ_succ] at hrow
    change ∑ j : Fin n, d.transition i.succ j.succ ≤ 1
    linarith [d.substochastic.nonneg i.succ 0]

/-- The Schur residual is a right inverse of the principal transient block. -/
theorem one_sub_principalTransition_mul_principalGreenResidual :
    (1 - d.principalTransition) * d.principalGreenResidual = 1 := by
  have hfull : (1 - d.transition) * d.green = 1 := by
    rw [green]
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr d.transient)
  ext i j
  have hmain := congrArg
    (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ ↦ A i.succ j.succ) hfull
  have hzero := congrArg
    (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ ↦ A i.succ 0) hfull
  simp only [Matrix.mul_apply] at hmain hzero ⊢
  rw [Fin.sum_univ_succ] at hmain hzero
  simp only [Matrix.sub_apply, Matrix.one_apply, Fin.succ_inj,
    if_neg (Fin.succ_ne_zero _), zero_sub] at hmain hzero
  simp only [principalTransition, principalGreenResidual, Matrix.sub_apply,
    Matrix.submatrix_apply, Matrix.one_apply]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hmain' :
      (∑ k, ((if i = k then 1 else 0) - d.transition i.succ k.succ) *
        d.green k.succ j.succ) =
        (if i = j then 1 else 0) + d.transition i.succ 0 * d.green 0 j.succ := by
    linarith [hmain]
  have hzero' :
      (∑ k, ((if i = k then 1 else 0) - d.transition i.succ k.succ) *
        d.green k.succ 0) = d.transition i.succ 0 * d.green 0 0 := by
    linarith [hzero]
  have hfactor :
      (∑ k, ((if i = k then 1 else 0) - d.transition i.succ k.succ) *
        (d.green k.succ 0 * d.green 0 j.succ / d.green 0 0)) =
        (∑ k, ((if i = k then 1 else 0) - d.transition i.succ k.succ) *
          d.green k.succ 0) * d.green 0 j.succ / d.green 0 0 := by
    calc
      _ = ∑ k, (((if i = k then 1 else 0) - d.transition i.succ k.succ) *
          d.green k.succ 0) * d.green 0 j.succ / d.green 0 0 := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by
        simp only [div_eq_mul_inv]
        rw [← Finset.sum_mul, ← Finset.sum_mul]
  rw [hmain', hfactor, hzero']
  field_simp [ne_of_gt d.green_zero_zero_pos]
  ring

/-- The principal transient block remains nonsingular. -/
theorem principalTransition_transient : (1 - d.principalTransition).det ≠ 0 := by
  exact Matrix.det_ne_zero_of_right_inverse
    d.one_sub_principalTransition_mul_principalGreenResidual

/-- The principal Green matrix is the Schur residual of the full Green matrix. -/
theorem inv_one_sub_principalTransition_eq_principalGreenResidual :
    (1 - d.principalTransition)⁻¹ = d.principalGreenResidual := by
  exact Matrix.inv_eq_right_inv d.one_sub_principalTransition_mul_principalGreenResidual

/-- Entrywise form of the principal Green Schur formula. -/
theorem inv_one_sub_principalTransition_apply (i j : Fin n) :
    ((1 - d.principalTransition)⁻¹) i j =
      d.green i.succ j.succ - d.green i.succ 0 * d.green 0 j.succ / d.green 0 0 := by
  rw [d.inv_one_sub_principalTransition_eq_principalGreenResidual]
  rfl

/-- Every entry of the principal Green residual is nonnegative. -/
theorem principalGreenResidual_nonneg (i j : Fin n) :
    0 ≤ d.principalGreenResidual i j := by
  rw [← d.inv_one_sub_principalTransition_eq_principalGreenResidual]
  exact d.principalTransition_substochastic.inv_nonneg d.principalTransition_transient i j

/-- The entrywise Schur correction leaves a nonnegative residual. -/
theorem green_schur_residual_nonneg (i j : Fin n) :
    0 ≤ d.green i.succ j.succ -
      d.green i.succ 0 * d.green 0 j.succ / d.green 0 0 := by
  exact d.principalGreenResidual_nonneg i j

end SSPRK.PhaseTypeData
