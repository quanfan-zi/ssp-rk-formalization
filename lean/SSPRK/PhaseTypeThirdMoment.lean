import SSPRK.PhaseTypeReindex
import SSPRK.GreenReachability
import SSPRK.MomentMixture
import SSPRK.MomentClassOperations
import SSPRK.PhaseTypeElimination
import SSPRK.PhaseTypeBlockMoments
import SSPRK.PhaseTypePrincipal

/-! The first three Green moments of a finite phase-type representation. -/

open scoped BigOperators

namespace SSPRK.PhaseTypeData

theorem green_reindex {s : ℕ} (d : PhaseTypeData s) (e : Fin s ≃ Fin s) :
    (d.reindex e).green = d.green.submatrix e e := by
  unfold green
  change (1 - d.transition.submatrix e e)⁻¹ = ((1 - d.transition)⁻¹).submatrix e e
  rw [show 1 - d.transition.submatrix e e = (1 - d.transition).submatrix e e by
    ext i j
    simp [Matrix.one_apply]]
  exact Matrix.inv_submatrix_equiv _ e e

theorem green_pow_reindex {s : ℕ} (d : PhaseTypeData s) (e : Fin s ≃ Fin s) (k : ℕ) :
    (d.reindex e).green ^ k = (d.green ^ k).submatrix e e := by
  rw [green_reindex]
  induction k with
  | zero => exact (Matrix.submatrix_one_equiv e).symm
  | succ k ih =>
    rw [pow_succ, pow_succ, ih]
    exact Matrix.submatrix_mul_equiv _ _ e e e

theorem green_pow_mulVec_one_reindex {s : ℕ} (d : PhaseTypeData s)
    (e : Fin s ≃ Fin s) (k : ℕ) (i : Fin s) :
    ((d.reindex e).green ^ k).mulVec (fun _ ↦ 1) i =
      (d.green ^ k).mulVec (fun _ ↦ 1) (e i) := by
  rw [green_pow_reindex, Matrix.submatrix_mulVec_equiv]
  rfl

theorem green_entry_nonneg {s : ℕ} (d : PhaseTypeData s) (i j : Fin s) :
    0 ≤ d.green i j :=
  d.substochastic.inv_nonneg d.transient i j

theorem green_rowSum_pos {s : ℕ} (d : PhaseTypeData s) (i : Fin s) :
    0 < d.green.mulVec (fun _ ↦ 1) i :=
  lt_of_lt_of_le zero_lt_one (d.substochastic.one_le_inv_mulVec_one d.transient i)

theorem green_moment_class_of_rows {s : ℕ} (d : PhaseTypeData s)
    (hrow : ∀ i, MomentClass s (d.green.mulVec (fun _ ↦ 1) i)
      (2 * (d.green ^ 2).mulVec (fun _ ↦ 1) i)
      (6 * (d.green ^ 3).mulVec (fun _ ↦ 1) i))
    (hmean : 0 < dotProduct d.initial (d.green.mulVec (fun _ ↦ 1))) :
    MomentClass s (dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)))
      (2 * dotProduct d.initial ((d.green ^ 2).mulVec (fun _ ↦ 1)))
      (6 * dotProduct d.initial ((d.green ^ 3).mulVec (fun _ ↦ 1))) := by
  convert MomentClass.finite_mixture d.initial _ _ _ d.initial_nonneg
    d.initial_mass_le hrow hmean using 1 <;>
    simp only [dotProduct, Finset.mul_sum, mul_left_comm]

noncomputable def normalizedGreen {n : ℕ} (d : PhaseTypeData (n + 1)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (d.green 0 0)⁻¹ • d.green

theorem green_pivot_pos {n : ℕ} (d : PhaseTypeData (n + 1)) : 0 < d.green 0 0 :=
  lt_of_lt_of_le zero_lt_one (d.substochastic.one_le_inv_diag d.transient 0)

theorem normalizedGreen_zero_zero {n : ℕ} (d : PhaseTypeData (n + 1)) :
    d.normalizedGreen 0 0 = 1 := by
  simp [normalizedGreen, d.green_pivot_pos.ne']

theorem normalizedGreen_nonneg {n : ℕ} (d : PhaseTypeData (n + 1)) (i j) :
    0 ≤ d.normalizedGreen i j :=
  mul_nonneg (inv_nonneg.mpr d.green_pivot_pos.le) (d.green_entry_nonneg i j)

theorem normalizedGreen_power_row {n : ℕ} (d : PhaseTypeData (n + 1)) (k : ℕ) (i) :
    (d.normalizedGreen ^ k).mulVec (fun _ ↦ 1) i =
      (d.green 0 0)⁻¹ ^ k * (d.green ^ k).mulVec (fun _ ↦ 1) i := by
  simp only [normalizedGreen, smul_pow, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]

theorem normalizedGreen_blockU {n : ℕ} (d : PhaseTypeData (n + 1)) :
    phaseBlockU d.normalizedGreen = (d.green 0 0)⁻¹ • (fun j ↦ d.green 0 j.succ) := rfl

theorem normalizedGreen_blockW {n : ℕ} (d : PhaseTypeData (n + 1)) :
    phaseBlockW d.normalizedGreen = (d.green 0 0)⁻¹ • d.eliminateZero.green := by
  ext i j
  simp [phaseBlockW, normalizedGreen]

theorem normalizedGreen_z1 {n : ℕ} (d : PhaseTypeData (n + 1)) :
    phaseBlockZ1 d.normalizedGreen = (d.green 0 0)⁻¹ *
      dotProduct d.eliminateZero.initial (d.eliminateZero.green.mulVec (fun _ ↦ 1)) := by
  rw [phaseBlockZ1, normalizedGreen_blockU, smul_dotProduct, smul_eq_mul,
    Matrix.dotProduct_mulVec, d.eliminateZero_vecMul_green]

theorem normalizedGreen_z2 {n : ℕ} (d : PhaseTypeData (n + 1)) :
    phaseBlockZ2 d.normalizedGreen = (d.green 0 0)⁻¹ ^ 2 *
      (2 * dotProduct d.eliminateZero.initial
        ((d.eliminateZero.green ^ 2).mulVec (fun _ ↦ 1))) := by
  rw [phaseBlockZ2, normalizedGreen_blockU, normalizedGreen_blockW,
    Matrix.smul_mulVec, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  rw [pow_two d.eliminateZero.green, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec d.eliminateZero.initial,
    d.eliminateZero_vecMul_green]
  ring

theorem normalizedGreen_z3 {n : ℕ} (d : PhaseTypeData (n + 1)) :
    phaseBlockZ3 d.normalizedGreen = (d.green 0 0)⁻¹ ^ 3 *
      (6 * dotProduct d.eliminateZero.initial
        ((d.eliminateZero.green ^ 3).mulVec (fun _ ↦ 1))) := by
  rw [phaseBlockZ3, normalizedGreen_blockU, normalizedGreen_blockW]
  simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  rw [show d.eliminateZero.green ^ 3 =
      d.eliminateZero.green * (d.eliminateZero.green * d.eliminateZero.green) by
      rw [pow_succ, pow_two, mul_assoc],
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec d.eliminateZero.initial,
    d.eliminateZero_vecMul_green]
  ring

theorem normalizedGreen_blockU_eq_zero {n : ℕ} (d : PhaseTypeData (n + 1))
    (hzero : phaseBlockZ1 d.normalizedGreen = 0) :
    phaseBlockU d.normalizedGreen = 0 := by
  have hsum : ∑ i, phaseBlockU d.normalizedGreen i = 0 := by
    simpa only [phaseBlockZ1, dotProduct, mul_one] using hzero
  funext i
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦
    d.normalizedGreen_nonneg 0 j.succ)).mp hsum i (Finset.mem_univ i)

theorem phaseBlock_momentClass_of_tail {n : ℕ}
    (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hG : G 0 0 = 1)
    (hη1 : 0 ≤ phaseBlockEta1 G) (hη2 : 0 ≤ phaseBlockEta2 G)
    (hclass : MomentClass n (phaseBlockZ1 G) (phaseBlockZ2 G) (phaseBlockZ3 G)) :
    MomentClass (n + 1 : ℕ) (phaseBlockMoment G 1)
      (phaseBlockMoment G 2) (phaseBlockMoment G 3) := by
  rw [phaseBlock_first_moment G hG, phaseBlock_second_moment G hG,
    phaseBlock_third_moment G hG]
  convert hclass.add (auxiliary_moment_class hη1 hη2) using 1 <;> push_cast <;> ring

theorem phaseBlock_momentClass_of_upper_zero {n : ℕ}
    (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hG : G 0 0 = 1)
    (hU : phaseBlockU G = 0) :
    MomentClass (n + 1 : ℕ) (phaseBlockMoment G 1)
      (phaseBlockMoment G 2) (phaseBlockMoment G 3) := by
  have hclass : MomentClass 1 1 2 6 := by
    simpa using auxiliary_moment_class (le_refl (0 : ℝ)) (le_refl (0 : ℝ))
  have hle : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_add_left 1 n
  convert hclass.mono_parameter hle using 1 <;>
    simp [phaseBlock_first_moment G hG, phaseBlock_second_moment G hG,
      phaseBlock_third_moment G hG, phaseBlockZ1, phaseBlockZ2, phaseBlockZ3,
      phaseBlockEta1, phaseBlockEta2, hU]

theorem green_row_momentClass_of_normalized {n : ℕ} (d : PhaseTypeData (n + 1))
    (hclass : MomentClass (n + 1 : ℕ) (phaseBlockMoment d.normalizedGreen 1)
      (phaseBlockMoment d.normalizedGreen 2) (phaseBlockMoment d.normalizedGreen 3)) :
    MomentClass (n + 1 : ℕ) (d.green.mulVec (fun _ ↦ 1) 0)
      (2 * (d.green ^ 2).mulVec (fun _ ↦ 1) 0)
      (6 * (d.green ^ 3).mulVec (fun _ ↦ 1) 0) := by
  convert hclass.scale d.green_pivot_pos using 1 <;>
    simp only [phaseBlockMoment] <;>
    rw [normalizedGreen_power_row] <;> norm_num <;>
    field_simp [d.green_pivot_pos.ne']

theorem normalizedGreen_eta1_nonneg {n : ℕ} (d : PhaseTypeData (n + 1)) :
    0 ≤ phaseBlockEta1 d.normalizedGreen := by
  unfold phaseBlockEta1 dotProduct phaseBlockU phaseBlockV
  exact Finset.sum_nonneg fun i _ ↦
    mul_nonneg (d.normalizedGreen_nonneg 0 i.succ) (d.normalizedGreen_nonneg i.succ 0)

theorem normalizedGreen_eta2_nonneg {n : ℕ} (d : PhaseTypeData (n + 1))
    (hH : ∀ i j, 0 ≤ phaseBlockH d.normalizedGreen i j) :
    0 ≤ phaseBlockEta2 d.normalizedGreen := by
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
  simp only [Matrix.mulVec, dotProduct, phaseBlockU, phaseBlockV]
  exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (d.normalizedGreen_nonneg 0 i.succ)
    (Finset.sum_nonneg fun j _ ↦ mul_nonneg (hH i j) (d.normalizedGreen_nonneg j.succ 0))

theorem green_zero_momentClass_of_induction {n : ℕ} (d : PhaseTypeData (n + 1))
    (ih : ∀ e : PhaseTypeData n,
      0 < dotProduct e.initial (e.green.mulVec (fun _ ↦ 1)) →
      MomentClass n (dotProduct e.initial (e.green.mulVec (fun _ ↦ 1)))
        (2 * dotProduct e.initial ((e.green ^ 2).mulVec (fun _ ↦ 1)))
        (6 * dotProduct e.initial ((e.green ^ 3).mulVec (fun _ ↦ 1))))
    (hH : ∀ i j, 0 ≤ phaseBlockH d.normalizedGreen i j) :
    MomentClass (n + 1 : ℕ) (d.green.mulVec (fun _ ↦ 1) 0)
      (2 * (d.green ^ 2).mulVec (fun _ ↦ 1) 0)
      (6 * (d.green ^ 3).mulVec (fun _ ↦ 1) 0) := by
  apply d.green_row_momentClass_of_normalized
  have hz : 0 ≤ phaseBlockZ1 d.normalizedGreen := by
    simpa only [phaseBlockZ1, dotProduct, mul_one] using
      Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) ↦ d.normalizedGreen_nonneg 0 j.succ)
  obtain hzero | hpos := hz.eq_or_lt
  · exact phaseBlock_momentClass_of_upper_zero _ d.normalizedGreen_zero_zero
      (d.normalizedGreen_blockU_eq_zero hzero.symm)
  · have hmean : 0 < dotProduct d.eliminateZero.initial
        (d.eliminateZero.green.mulVec (fun _ ↦ 1)) := by
      rw [d.normalizedGreen_z1] at hpos
      exact (mul_pos_iff_of_pos_left (inv_pos.mpr d.green_pivot_pos)).mp hpos
    apply phaseBlock_momentClass_of_tail _ d.normalizedGreen_zero_zero
      d.normalizedGreen_eta1_nonneg (d.normalizedGreen_eta2_nonneg hH)
    rw [d.normalizedGreen_z1, d.normalizedGreen_z2, d.normalizedGreen_z3]
    exact (ih d.eliminateZero hmean).scale (inv_pos.mpr d.green_pivot_pos)

theorem normalizedGreen_blockH_nonneg {n : ℕ} (d : PhaseTypeData (n + 1)) (i j) :
    0 ≤ phaseBlockH d.normalizedGreen i j := by
  have hid : phaseBlockH d.normalizedGreen i j =
      (d.green 0 0)⁻¹ * d.principalGreenResidual i j := by
    simp only [phaseBlockH, phaseBlockW, phaseBlockU, phaseBlockV, normalizedGreen,
      principalGreenResidual, Matrix.sub_apply, Matrix.vecMulVec_apply,
      Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hid]
  exact mul_nonneg (inv_nonneg.mpr d.green_pivot_pos.le)
    (d.principalGreenResidual_nonneg i j)

/-- Every finite phase-type representation satisfies the first three moment bounds. -/
theorem green_moment_class (s : ℕ) (d : PhaseTypeData s)
    (hmean : 0 < dotProduct d.initial (d.green.mulVec (fun _ ↦ 1))) :
    MomentClass s (dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)))
      (2 * dotProduct d.initial ((d.green ^ 2).mulVec (fun _ ↦ 1)))
      (6 * dotProduct d.initial ((d.green ^ 3).mulVec (fun _ ↦ 1))) := by
  induction s with
  | zero =>
    simp only [dotProduct, Finset.univ_eq_empty, Finset.sum_empty, lt_self_iff_false] at hmean
  | succ n ih =>
    apply d.green_moment_class_of_rows _ hmean
    intro i
    let e : Fin (n + 1) ≃ Fin (n + 1) := Equiv.swap 0 i
    have hzero := (d.reindex e).green_zero_momentClass_of_induction ih
      (d.reindex e).normalizedGreen_blockH_nonneg
    have hrow (k : ℕ) := d.green_pow_mulVec_one_reindex e k 0
    have he : e 0 = i := Equiv.swap_apply_left 0 i
    simp only [he] at hrow
    have hfirst := hrow 1
    simp only [pow_one] at hfirst
    rw [hfirst, hrow 2, hrow 3] at hzero
    exact hzero

end SSPRK.PhaseTypeData
