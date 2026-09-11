import SSPRK.Substochastic

/-!
# Rows of an equality-case phase chain

When a sorted row can only stay at its level or move down one level, the mean balance
determines its diagonal and downward transition probabilities.
-/

open scoped BigOperators

namespace SSPRK

theorem phase_chain_row_weighted_sum {s : ℕ} (P : Matrix (Fin s) (Fin s) ℝ)
    (a : ℝ) (j : Fin s)
    (hsupport : ∀ k, P j k ≠ 0 → k = j ∨ j.val = k.val + 1) :
    (∑ k, P j k * ((k.val + 1 : ℝ) * a)) =
      (j.val : ℝ) * a * (∑ k, P j k) + a * P j j := by
  calc
    _ = ∑ k, ((j.val : ℝ) * a * P j k + if k = j then a * P j j else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hkj : k = j
      · subst k
        simp only [ite_true]
        ring
      · simp only [if_neg hkj, add_zero]
        by_cases hzero : P j k = 0
        · simp [hzero]
        · have hv := (hsupport k hzero).resolve_left hkj
          have hv' : (j.val : ℝ) = k.val + 1 := by exact_mod_cast hv
          rw [hv']
          ring
    _ = _ := by simp [Finset.sum_add_distrib, ← Finset.mul_sum]

theorem phase_chain_row_diagonal {s : ℕ} (P : Matrix (Fin s) (Fin s) ℝ)
    {a : ℝ} (ha : 0 < a) (j : Fin s)
    (hsupport : ∀ k, P j k ≠ 0 → k = j ∨ j.val = k.val + 1)
    (hexit : j.val ≠ 0 → ∑ k, P j k = 1)
    (hbalance : (j.val + 1 : ℝ) * a - ∑ k, P j k * ((k.val + 1 : ℝ) * a) = 1) :
    P j j = 1 - 1 / a := by
  rw [phase_chain_row_weighted_sum P a j hsupport] at hbalance
  have hx : (j.val : ℝ) * a * (∑ k, P j k) = j.val * a := by
    by_cases hj : j.val = 0
    · simp [hj]
    · rw [hexit hj, mul_one]
  rw [hx] at hbalance
  field_simp
  nlinarith

theorem phase_chain_row_predecessor {s : ℕ} (P : Matrix (Fin s) (Fin s) ℝ)
    {a : ℝ} (ha : 0 < a) (j : Fin s)
    (hsupport : ∀ k, P j k ≠ 0 → k = j ∨ j.val = k.val + 1)
    (hexit : j.val ≠ 0 → ∑ k, P j k = 1)
    (hbalance : (j.val + 1 : ℝ) * a - ∑ k, P j k * ((k.val + 1 : ℝ) * a) = 1)
    (k : Fin s) (hpred : j.val = k.val + 1) : P j k = 1 / a := by
  have hdiag := phase_chain_row_diagonal P ha j hsupport hexit hbalance
  have hrow := hexit (by omega)
  have hsum : (∑ l, P j l) = P j j + P j k := by
    apply Fintype.sum_eq_add j k (by intro h; subst k; omega)
    intro l hl
    by_contra hnonzero
    rcases hsupport l hnonzero with h | h
    · exact hl.1 h
    · apply hl.2
      apply Fin.ext
      omega
  rw [hsum, hdiag] at hrow
  linarith

theorem phase_chain_row_form {s : ℕ} (P : Matrix (Fin s) (Fin s) ℝ)
    {a : ℝ} (ha : 0 < a) (j : Fin s)
    (hsupport : ∀ k, P j k ≠ 0 → k = j ∨ j.val = k.val + 1)
    (hexit : j.val ≠ 0 → ∑ k, P j k = 1)
    (hbalance : (j.val + 1 : ℝ) * a - ∑ k, P j k * ((k.val + 1 : ℝ) * a) = 1) :
    ∀ k, P j k = if j = k then 1 - 1 / a else if j.val = k.val + 1 then 1 / a else 0 := by
  intro k
  split_ifs with hself hpred
  · subst k
    exact phase_chain_row_diagonal P ha j hsupport hexit hbalance
  · exact phase_chain_row_predecessor P ha j hsupport hexit hbalance k hpred
  · by_contra hnonzero
    rcases hsupport k hnonzero with h | h
    · exact hself h.symm
    · exact hpred h

theorem phase_chain_row_downward_exists {s : ℕ} (P : Matrix (Fin s) (Fin s) ℝ)
    {a : ℝ} (ha : 0 < a) (j : Fin s)
    (hsupport : ∀ k, P j k ≠ 0 → k = j ∨ j.val = k.val + 1)
    (hexit : j.val ≠ 0 → ∑ k, P j k = 1)
    (hbalance : (j.val + 1 : ℝ) * a - ∑ k, P j k * ((k.val + 1 : ℝ) * a) = 1)
    (hj : 0 < j.val) : ∃ k : Fin s, j.val = k.val + 1 ∧ P j k = 1 / a ∧ 0 < P j k := by
  let k : Fin s := ⟨j.val - 1, by omega⟩
  have hpred : j.val = k.val + 1 := by dsimp [k]; omega
  have hp := phase_chain_row_predecessor P ha j hsupport hexit hbalance k hpred
  exact ⟨k, hpred, hp, hp.symm ▸ one_div_pos.mpr ha⟩

end SSPRK
