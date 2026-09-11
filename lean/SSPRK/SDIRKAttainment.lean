import SSPRK.Feasibility
import SSPRK.SDIRKOrder

/-!
# Absolute-monotonicity feasibility of the third-order SDIRK family

The shifted SDIRK tableau is a positive scalar multiple of the finite chain matrix, so its
inverse and transformed output are explicit.
-/

open scoped BigOperators ENNReal

namespace SSPRK

noncomputable section

lemma thirdOrderRadius_eq_sdirkT_mul_sdirkD {s : ℕ} (hs : 2 ≤ s) :
    thirdOrderRadius s = sdirkT s * sdirkD s := by
  change (s : ℝ) - 1 + sdirkT s =
    sdirkT s * (1 + ((s : ℝ) - 1) / sdirkT s)
  have ht : sdirkT s ≠ 0 := ne_of_gt (sdirkT_pos hs)
  field_simp [ht]
  ring

lemma sdirk_inverse_certificate {s : ℕ} (hs : 2 ≤ s) :
    (1 + thirdOrderRadius s • sdirkA s) * (sdirkD s)⁻¹ • chainD s = 1 := by
  rw [sdirk_shifted_eq_chainL hs, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    chainL_mul_chainD]
  rw [mul_inv_cancel₀ (ne_of_gt (sdirkD_pos hs)), one_smul]

lemma sdirk_output_inverse_apply {s : ℕ} (hs : 2 ≤ s) (i : Fin s) :
    Matrix.vecMul (sdirkB s) ((sdirkD s)⁻¹ • chainD s) i =
      if i.val + 1 = s then 1 / ((s : ℝ) * sdirkD s) else 0 := by
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hsne : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hspos)
  have hdne : sdirkD s ≠ 0 := ne_of_gt (sdirkD_pos hs)
  have hb : sdirkB s = (1 / (s : ℝ)) • ones s := by
    ext j
    simp [sdirkB, ones]
  rw [hb, Matrix.smul_vecMul, Matrix.vecMul_smul]
  simp only [Pi.smul_apply, smul_eq_mul, ones_vecMul_chainD]
  split_ifs
  · field_simp [hsne, hdne]
  · simp

lemma sdirk_output_inverse_sum {s : ℕ} (hs : 2 ≤ s) :
    dotProduct (Matrix.vecMul (sdirkB s) ((sdirkD s)⁻¹ • chainD s)) (ones s) =
      1 / ((s : ℝ) * sdirkD s) := by
  let last : Fin s := ⟨s - 1, by omega⟩
  have hlast (i : Fin s) : i.val + 1 = s ↔ i = last := by
    constructor
    · intro h
      apply Fin.ext
      dsimp [last]
      omega
    · intro h
      subst i
      dsimp [last]
      omega
  simp only [dotProduct, sdirk_output_inverse_apply hs, ones, mul_one, hlast]
  simp

lemma sdirk_output_mass_eq {s : ℕ} (hs : 2 ≤ s) :
    thirdOrderRadius s * (1 / ((s : ℝ) * sdirkD s)) = sdirkT s / (s : ℝ) := by
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hsne : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hspos)
  have hdne : sdirkD s ≠ 0 := ne_of_gt (sdirkD_pos hs)
  rw [thirdOrderRadius_eq_sdirkT_mul_sdirkD hs]
  field_simp [hsne, hdne]

theorem sdirk_feasible {s : ℕ} (hs : 2 ≤ s) :
    AbsolutelyMonotoneAt (sdirkA s) (sdirkB s) (thirdOrderRadius s) := by
  refine AbsolutelyMonotoneAt.of_inverse (sdirkA s) (sdirkB s) (thirdOrderRadius s)
    ((sdirkD s)⁻¹ • chainD s) (sdirk_inverse_certificate hs) ?_ ?_ ?_ ?_
  · intro i
    change 0 ≤ (((sdirkD s)⁻¹ • chainD s).mulVec (ones s)) i
    have hdpos : 0 < sdirkD s := sdirkD_pos hs
    rw [Matrix.smul_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul, chainD_mulVec_ones]
    split_ifs <;> simp [inv_nonneg.mpr hdpos.le]
  · have hdpos : 0 < sdirkD s := sdirkD_pos hs
    have hdinv : 0 ≤ (sdirkD s)⁻¹ := inv_nonneg.mpr hdpos.le
    have hdinvle : (sdirkD s)⁻¹ ≤ 1 := (inv_le_one₀ hdpos).mpr (one_le_sdirkD hs)
    intro i j
    simp [chainD, shiftDown, Matrix.sub_apply, Matrix.one_apply]
    split_ifs <;> linarith
  · intro i
    have hspos : 0 < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
    have hdpos : 0 < sdirkD s := sdirkD_pos hs
    rw [sdirk_output_inverse_apply hs]
    split_ifs
    · exact (div_pos zero_lt_one (mul_pos hspos hdpos)).le
    · exact le_rfl
  · change thirdOrderRadius s * dotProduct
      (Matrix.vecMul (sdirkB s) ((sdirkD s)⁻¹ • chainD s)) (ones s) ≤ 1
    rw [sdirk_output_inverse_sum hs, sdirk_output_mass_eq hs]
    linarith [sdirkT_div_lt_one hs]

end

end SSPRK
