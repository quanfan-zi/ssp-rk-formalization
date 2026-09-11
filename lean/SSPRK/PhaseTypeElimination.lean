import SSPRK.PhaseTypeData

/-!
# Eliminating the first transient state

The Schur complement of the first diagonal entry gives a smaller uniformized
phase-type representation. This module establishes the matrix construction and
its Green identities; it does not identify a continuous-time occupation law.
-/

open scoped BigOperators

namespace SSPRK.PhaseTypeData

variable {n : ℕ} (d : PhaseTypeData (n + 1))

noncomputable def eliminationPivot : ℝ := 1 - d.transition 0 0

theorem eliminationPivot_pos : 0 < d.eliminationPivot := by
  have hle := d.substochastic.entry_le_one 0 0
  apply sub_pos.mpr
  by_contra hlt
  have he : d.transition 0 0 = 1 := le_antisymm hle (le_of_not_gt hlt)
  have hsum : (∑ k : Fin n, d.transition 0 k.succ) ≤ 0 := by
    have hrow := d.substochastic.row_sum_le 0
    rw [Fin.sum_univ_succ, he] at hrow
    linarith
  have hz (k : Fin n) : d.transition 0 k.succ = 0 := by
    have hk := Finset.single_le_sum
      (fun l (_ : l ∈ (Finset.univ : Finset (Fin n))) ↦ d.substochastic.nonneg 0 l.succ)
      (Finset.mem_univ k)
    exact le_antisymm (hk.trans hsum) (d.substochastic.nonneg 0 k.succ)
  apply d.transient
  apply Matrix.det_eq_zero_of_row_eq_zero (0 : Fin (n + 1))
  intro k
  refine Fin.cases ?_ (fun k ↦ ?_) k
  · simp [Matrix.sub_apply, he]
  · simp [Matrix.sub_apply, hz, Ne.symm (Fin.succ_ne_zero k)]

noncomputable def eliminationTransition : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ d.transition i.succ j.succ +
    d.transition i.succ 0 * d.transition 0 j.succ / d.eliminationPivot

noncomputable def eliminationInitial : Fin n → ℝ :=
  fun i ↦ d.transition 0 i.succ / d.eliminationPivot

theorem eliminationInitial_nonneg (i : Fin n) : 0 ≤ d.eliminationInitial i :=
  div_nonneg (d.substochastic.nonneg 0 i.succ) d.eliminationPivot_pos.le

theorem eliminationInitial_mass_le : ∑ i, d.eliminationInitial i ≤ 1 := by
  simp only [eliminationInitial, ← Finset.sum_div]
  apply (div_le_one d.eliminationPivot_pos).2
  have h := d.substochastic.row_sum_le 0
  rw [Fin.sum_univ_succ] at h
  unfold eliminationPivot
  linarith

theorem eliminationTransition_substochastic : Substochastic d.eliminationTransition := by
  constructor
  · intro i j
    exact add_nonneg (d.substochastic.nonneg i.succ j.succ)
      (div_nonneg (mul_nonneg (d.substochastic.nonneg i.succ 0)
        (d.substochastic.nonneg 0 j.succ)) d.eliminationPivot_pos.le)
  · intro i
    have h := d.substochastic.row_sum_le i.succ
    rw [Fin.sum_univ_succ] at h
    have hm := mul_le_mul_of_nonneg_left d.eliminationInitial_mass_le
      (d.substochastic.nonneg i.succ 0)
    calc
      _ = (∑ j : Fin n, d.transition i.succ j.succ) +
          d.transition i.succ 0 * ∑ j, d.eliminationInitial j := by
        simp [eliminationTransition, eliminationInitial, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.sum_div, mul_div_assoc]
      _ ≤ 1 := by linarith

theorem elimination_green_balance (i j : Fin (n + 1)) :
    d.green i j - ∑ k, d.transition i k * d.green k j =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j := by
  have h := Matrix.mul_nonsing_inv (1 - d.transition) (isUnit_iff_ne_zero.mpr d.transient)
  rw [Matrix.sub_mul, Matrix.one_mul] at h
  simpa only [Matrix.sub_apply, Matrix.mul_apply, green] using
    congrArg (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ ↦ A i j) h

theorem eliminationInitial_mul_green (j : Fin n) :
    (∑ i, d.eliminationInitial i * d.green i.succ j.succ) = d.green 0 j.succ := by
  have h := d.elimination_green_balance 0 j.succ
  rw [Fin.sum_univ_succ] at h
  simp only [Matrix.one_apply, if_neg (Ne.symm (Fin.succ_ne_zero j))] at h
  simp only [eliminationInitial, div_mul_eq_mul_div, ← Finset.sum_div]
  apply (div_eq_iff (ne_of_gt d.eliminationPivot_pos)).2
  unfold eliminationPivot
  nlinarith only [h]

theorem elimination_schur_mul_green :
    (1 - d.eliminationTransition) * (d.green.submatrix Fin.succ Fin.succ) = 1 := by
  ext i j
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.mul_apply]
  simp only [Matrix.submatrix_apply]
  have h := d.elimination_green_balance i.succ j.succ
  rw [Fin.sum_univ_succ] at h
  have hentry (k : Fin n) : d.eliminationTransition i k * d.green k.succ j.succ =
      d.transition i.succ k.succ * d.green k.succ j.succ +
        d.transition i.succ 0 * (d.eliminationInitial k * d.green k.succ j.succ) := by
    unfold eliminationTransition eliminationInitial
    ring
  simp_rw [hentry]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, d.eliminationInitial_mul_green]
  have hid : (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i.succ j.succ =
      (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    simp [Matrix.one_apply, Fin.succ_inj]
  rw [hid] at h
  linarith

theorem eliminationTransition_transient : (1 - d.eliminationTransition).det ≠ 0 := by
  have h := congrArg Matrix.det d.elimination_schur_mul_green
  rw [Matrix.det_mul, Matrix.det_one] at h
  intro hz
  rw [hz, zero_mul] at h
  norm_num at h

/-- The smaller transient representation obtained by deleting state zero. -/
noncomputable def eliminateZero : PhaseTypeData n where
  transition := d.eliminationTransition
  initial := d.eliminationInitial
  rate := d.rate
  rate_pos := d.rate_pos
  substochastic := d.eliminationTransition_substochastic
  transient := d.eliminationTransition_transient
  initial_nonneg := d.eliminationInitial_nonneg
  initial_mass_le := d.eliminationInitial_mass_le

theorem eliminateZero_green :
    d.eliminateZero.green = d.green.submatrix Fin.succ Fin.succ := by
  exact Matrix.inv_eq_right_inv d.elimination_schur_mul_green

theorem eliminateZero_initial_mul_green (j : Fin n) :
    (∑ i, d.eliminateZero.initial i * d.eliminateZero.green i j) = d.green 0 j.succ := by
  rw [d.eliminateZero_green]
  exact d.eliminationInitial_mul_green j

theorem eliminateZero_vecMul_green :
    Matrix.vecMul d.eliminateZero.initial d.eliminateZero.green =
      fun j ↦ d.green 0 j.succ := by
  funext j
  exact d.eliminateZero_initial_mul_green j

@[simp] theorem eliminateZero_rate : d.eliminateZero.rate = d.rate := rfl

@[simp] theorem eliminateZero_transition (i j : Fin n) :
    d.eliminateZero.transition i j = d.transition i.succ j.succ +
      d.transition i.succ 0 * d.transition 0 j.succ / (1 - d.transition 0 0) := rfl

@[simp] theorem eliminateZero_initial (i : Fin n) :
    d.eliminateZero.initial i = d.transition 0 i.succ / (1 - d.transition 0 0) := rfl

@[simp] theorem eliminateZero_green_apply (i j : Fin n) :
    d.eliminateZero.green i j = d.green i.succ j.succ := by
  rw [d.eliminateZero_green]
  rfl

end SSPRK.PhaseTypeData
