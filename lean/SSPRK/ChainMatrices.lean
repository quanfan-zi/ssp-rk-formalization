import SSPRK.RKTransform

open scoped BigOperators

namespace SSPRK

noncomputable section

def chainL (s : ℕ) : Matrix (Fin s) (Fin s) ℝ := fun i j ↦ if j ≤ i then 1 else 0

def shiftDown (s : ℕ) : Matrix (Fin s) (Fin s) ℝ :=
  fun i j ↦ if i.val = j.val + 1 then 1 else 0

def chainD (s : ℕ) : Matrix (Fin s) (Fin s) ℝ := 1 - shiftDown s

lemma fin_sum_val_ite {s n : ℕ} (hn : n < s) (f : Fin s → ℝ) :
    (∑ x : Fin s, if x.val = n then f x else 0) = f ⟨n, hn⟩ := by
  let k : Fin s := ⟨n, hn⟩
  calc
    (∑ x : Fin s, if x.val = n then f x else 0) = ∑ x : Fin s, if x = k then f x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      have hx : x.val = n ↔ x = k := by
        constructor
        · intro h
          apply Fin.ext
          simpa [k] using h
        · intro h
          simp [h, k]
      simp [hx]
    _ = f k := Fintype.sum_ite_eq' k f

lemma chainL_mul_shiftDown (s : ℕ) : chainL s * shiftDown s = chainL s - 1 := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  simp only [chainL, shiftDown, mul_ite, mul_one, mul_zero]
  change (∑ x : Fin s, if x.val = j.val + 1 then (if x ≤ i then (1 : ℝ) else 0) else 0) =
    (if j ≤ i then (1 : ℝ) else 0) - (if i = j then 1 else 0)
  by_cases hlast : j.val + 1 < s
  · let k : Fin s := ⟨j.val + 1, hlast⟩
    have hsum : (∑ x : Fin s, if x.val = j.val + 1 then (if x ≤ i then (1 : ℝ) else 0) else 0) =
        if k ≤ i then (1 : ℝ) else 0 := by
      calc
        (∑ x : Fin s, if x.val = j.val + 1 then (if x ≤ i then (1 : ℝ) else 0) else 0) =
            (∑ x : Fin s, if x = k then (if x ≤ i then (1 : ℝ) else 0) else 0) := by
              apply Finset.sum_congr rfl
              intro x _
              have hx : x.val = j.val + 1 ↔ x = k := by
                constructor
                · intro h
                  apply Fin.ext
                  simpa [k] using h
                · intro h
                  simp [h, k]
              simp [hx]
        _ = if k ≤ i then (1 : ℝ) else 0 := Fintype.sum_ite_eq' k _
    rw [hsum]
    by_cases hji : j ≤ i
    · by_cases hiji : i = j
      · subst i
        have hki : ¬k ≤ j := by
          rw [Fin.le_iff_val_le_val]
          simp [k]
        simp [hki]
      · have hki : k ≤ i := by
          rw [Fin.le_iff_val_le_val]
          rw [Fin.le_iff_val_le_val] at hji
          have hji_lt : j.val < i.val := by
            omega
          simpa [k] using hji_lt
        simp [hji, hiji, hki]
    · have hki : ¬k ≤ i := by
        intro hki
        apply hji
        rw [Fin.le_iff_val_le_val]
        rw [Fin.le_iff_val_le_val] at hki
        have hki_val : j.val + 1 ≤ i.val := by
          simpa [k] using hki
        omega
      have hiji : ¬i = j := by
        intro hiji
        apply hji
        simp [hiji]
      simp [hji, hiji, hki]
  · have hsum : (∑ x : Fin s, if x.val = j.val + 1 then (if x ≤ i then (1 : ℝ) else 0) else 0) =
        0 := by
      apply Finset.sum_eq_zero
      intro x _
      by_cases hx : x.val = j.val + 1
      · exfalso
        apply hlast
        omega
      · simp [hx]
    rw [hsum]
    by_cases hji : j ≤ i
    · have hiji : i = j := by
        rw [Fin.le_iff_val_le_val] at hji
        apply Fin.ext
        omega
      simp [hiji]
    · have hiji : ¬i = j := by
        intro hiji
        apply hji
        simp [hiji]
      simp [hji, hiji]

lemma chainL_mul_chainD (s : ℕ) : chainL s * chainD s = 1 := by
  rw [chainD, Matrix.mul_sub, Matrix.mul_one, chainL_mul_shiftDown]
  exact sub_sub_cancel _ _

lemma chainD_mul_chainL (s : ℕ) : chainD s * chainL s = 1 := by
  have hdet : (chainD s).det ≠ 0 := by
    intro hzero
    have h := congrArg Matrix.det (chainL_mul_chainD s)
    simp [Matrix.det_mul, hzero] at h
  have hL : chainL s = (chainD s)⁻¹ := by
    have h := congrArg (fun Q : Matrix (Fin s) (Fin s) ℝ ↦ Q * (chainD s)⁻¹)
      (chainL_mul_chainD s)
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)] using h
  rw [hL]
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)

lemma chainL_nonneg (s : ℕ) : MatrixNonneg (chainL s) := by
  intro i j
  unfold chainL
  split_ifs <;> norm_num

lemma shiftDown_nonneg (s : ℕ) : MatrixNonneg (shiftDown s) := by
  intro i j
  unfold shiftDown
  split_ifs <;> norm_num

lemma shiftDown_mulVec_ones (s : ℕ) (i : Fin s) :
    Matrix.mulVec (shiftDown s) (ones s) i = if i.val = 0 then 0 else 1 := by
  classical
  simp only [Matrix.mulVec, dotProduct, shiftDown, ones, mul_one]
  by_cases hi : i.val = 0
  · simp [hi]
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hi
    have hns : n < s := by
      omega
    calc
      (∑ j : Fin s, if i.val = j.val + 1 then (1 : ℝ) else 0) =
          ∑ j : Fin s, if j.val = n then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro j _
            have hij : i.val = j.val + 1 ↔ j.val = n := by
              omega
            simp [hij]
      _ = 1 := by
        simpa using fin_sum_val_ite hns (fun _ : Fin s ↦ (1 : ℝ))
      _ = if i.val = 0 then 0 else 1 := by simp [hi]

lemma ones_vecMul_shiftDown (s : ℕ) (i : Fin s) :
    Matrix.vecMul (ones s) (shiftDown s) i = if i.val + 1 = s then 0 else 1 := by
  classical
  simp only [Matrix.vecMul, dotProduct, ones, shiftDown, one_mul]
  by_cases hi : i.val + 1 < s
  · calc
      (∑ j : Fin s, if j.val = i.val + 1 then (1 : ℝ) else 0) = 1 := by
        simpa using fin_sum_val_ite hi (fun _ : Fin s ↦ (1 : ℝ))
      _ = if i.val + 1 = s then 0 else 1 := by
        have hne : i.val + 1 ≠ s := by omega
        simp [hne]
  · have hsum : (∑ j : Fin s, if j.val = i.val + 1 then (1 : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : j.val = i.val + 1
      · exfalso
        apply hi
        omega
      · simp [hj]
    rw [hsum]
    have heq : i.val + 1 = s := by omega
    simp [heq]

lemma chainD_mulVec_ones (s : ℕ) (i : Fin s) :
    Matrix.mulVec (chainD s) (ones s) i = if i.val = 0 then 1 else 0 := by
  rw [chainD, Matrix.sub_mulVec, Matrix.one_mulVec]
  change ones s i - Matrix.mulVec (shiftDown s) (ones s) i = _
  rw [shiftDown_mulVec_ones]
  by_cases hi : i.val = 0 <;> simp [ones, hi]

lemma ones_vecMul_chainD (s : ℕ) (i : Fin s) :
    Matrix.vecMul (ones s) (chainD s) i = if i.val + 1 = s then 1 else 0 := by
  rw [chainD, Matrix.vecMul_sub, Matrix.vecMul_one]
  change ones s i - Matrix.vecMul (ones s) (shiftDown s) i = _
  rw [ones_vecMul_shiftDown]
  by_cases hi : i.val + 1 = s <;> simp [ones, hi]

end

end SSPRK
