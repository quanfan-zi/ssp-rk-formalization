import SSPRK.Feasibility
import SSPRK.MidpointOrder
import SSPRK.ChainMatrices

/-!
# Attainment of the second-order bound

The repeated implicit midpoint tableau from V1.6, equation (5.1), is feasible at `2s`.
Its explicit inverse has diagonal `1/2` and first subdiagonal `-1/2`.
-/

open scoped BigOperators ENNReal

namespace SSPRK

/-- At `2s`, the shifted midpoint tableau has every lower triangular entry equal to two. -/
theorem midpoint_shifted_matrix_apply {s : ℕ} (hs : 0 < s) (i j : Fin s) :
    (1 + (2 * (s : ℝ)) • midpointA s) i j = if j ≤ i then 2 else 0 := by
  have hs0 : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hs)
  by_cases hij : i = j
  · subst j
    simp [Matrix.add_apply, midpointA]
    field_simp [hs0]
    norm_num
  · by_cases hji : j < i
    · simp [Matrix.add_apply, midpointA, hij, hji, hji.le, hs0]
    · have hnle : ¬j ≤ i := by omega
      simp [Matrix.add_apply, midpointA, hij, hji, hnle]

/-- The shifted matrix at the candidate optimal radius is twice the chain Green matrix. -/
theorem midpoint_shifted_matrix {s : ℕ} (hs : 0 < s) :
    1 + (2 * (s : ℝ)) • midpointA s = (2 : ℝ) • chainL s := by
  ext i j
  rw [midpoint_shifted_matrix_apply hs]
  simp [chainL]

/-- An explicit inverse of the shifted midpoint tableau. -/
theorem midpoint_inverse_certificate {s : ℕ} (hs : 0 < s) :
    (1 + (2 * (s : ℝ)) • midpointA s) * ((1 / 2 : ℝ) • chainD s) = 1 := by
  rw [midpoint_shifted_matrix hs, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    chainL_mul_chainD]
  norm_num

/-- The inverse at `2s` is half the first-difference matrix. -/
theorem midpoint_inverse {s : ℕ} (hs : 0 < s) :
    (1 + (2 * (s : ℝ)) • midpointA s)⁻¹ = (1 / 2 : ℝ) • chainD s :=
  Matrix.inv_eq_right_inv (midpoint_inverse_certificate hs)

/-- The transformed output row has only its last entry nonzero. -/
theorem midpoint_output_inverse_apply {s : ℕ} (i : Fin s) :
    Matrix.vecMul (midpointB s) ((1 / 2 : ℝ) • chainD s) i =
      if i.val + 1 = s then 1 / (2 * (s : ℝ)) else 0 := by
  have hb : midpointB s = (1 / (s : ℝ)) • ones s := by
    ext j
    simp [midpointB, ones]
  rw [hb, Matrix.smul_vecMul, Matrix.vecMul_smul]
  simp only [Pi.smul_apply, smul_eq_mul, ones_vecMul_chainD]
  split_ifs <;> ring

/-- The output row of the inverse has total mass `1/(2s)`. -/
theorem midpoint_output_inverse_sum {s : ℕ} (hs : 0 < s) :
    dotProduct (Matrix.vecMul (midpointB s) ((1 / 2 : ℝ) • chainD s))
      (fun _ ↦ (1 : ℝ)) = 1 / (2 * (s : ℝ)) := by
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
  simp only [dotProduct, midpoint_output_inverse_apply, mul_one, hlast]
  simp

/-- The repeated implicit midpoint rule satisfies all complete SSP conditions at `2s`. -/
theorem midpoint_feasible {s : ℕ} (hs : 0 < s) :
    AbsolutelyMonotoneAt (midpointA s) (midpointB s) (2 * (s : ℝ)) := by
  refine AbsolutelyMonotoneAt.of_inverse (midpointA s) (midpointB s) (2 * (s : ℝ))
    ((1 / 2 : ℝ) • chainD s) (midpoint_inverse_certificate hs) ?_ ?_ ?_ ?_
  · intro i
    change 0 ≤ (((1 / 2 : ℝ) • chainD s).mulVec (ones s)) i
    rw [Matrix.smul_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul, chainD_mulVec_ones]
    split_ifs <;> norm_num
  · intro i j
    simp [chainD, shiftDown, Matrix.sub_apply, Matrix.one_apply]
    split_ifs <;> norm_num
  · intro i
    rw [midpoint_output_inverse_apply]
    split_ifs <;> positivity
  · rw [midpoint_output_inverse_sum hs]
    have hs0 : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hs)
    field_simp [hs0]
    exact le_rfl

/-- The complete radius of the repeated implicit midpoint rule is exactly `2s`. -/
theorem midpoint_radius {s : ℕ} (hs : 0 < s) :
    absoluteMonotonicityRadius (midpointA s) (midpointB s) =
      ENNReal.ofReal (2 * (s : ℝ)) := by
  apply le_antisymm
  · exact second_order_radius_bound hs (midpointA s) (midpointB s)
      (midpoint_order_one hs) (midpoint_order_two hs)
  · exact (midpoint_feasible hs).le_radius (by positivity)

end SSPRK
