import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A finite potential for the minimum-variance inequality

The potential is built by repeatedly removing a minimum coordinate. This is equivalent to
summing the squares of consecutive gaps between ordered levels, including the absorbing level zero.
-/

namespace SSPRK

private lemma square_add_bound (n a u v : ℝ) (hn : 0 < n) (h : u ^ 2 ≤ n * v) :
    (a + u) ^ 2 ≤ (n + 1) * (a ^ 2 + v) := by
  have hc : n * ((n + 1) * (a ^ 2 + v) - (a + u) ^ 2) =
      (n + 1) * (n * v - u ^ 2) + (u - n * a) ^ 2 := by ring
  have hnonneg : 0 ≤ n * ((n + 1) * (a ^ 2 + v) - (a + u) ^ 2) := by
    rw [hc]
    exact add_nonneg (mul_nonneg (by linarith) (sub_nonneg.mpr h)) (sq_nonneg _)
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hnonneg hn)

/-- Nonnegative coordinates admit a potential controlled by their squared differences. -/
theorem exists_variance_potential (s : ℕ) (m : Fin s → ℝ) (hm : ∀ i, 0 ≤ m i) :
    ∃ f : Fin s → ℝ, (∀ i, 0 ≤ f i) ∧ (∀ i, m i ^ 2 ≤ (s : ℝ) * f i) ∧
      (∀ i, f i ≤ m i ^ 2) ∧ (∀ i j, f i - f j ≤ (m i - m j) ^ 2) := by
  induction s with
  | zero => exact ⟨fun _ ↦ 0, by simp, by simp, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ m Finset.univ_nonempty
    obtain ⟨g, hg0, hgl, hgu, hgd⟩ := ih (fun i ↦ m (j.succAbove i) - m j)
      (fun i ↦ sub_nonneg.mpr (hj _ (Finset.mem_univ _)))
    refine ⟨j.insertNth (m j ^ 2) (fun i ↦ m j ^ 2 + g i), ?_, ?_, ?_, ?_⟩
    · intro i
      rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨i, rfl⟩
      · simp only [Fin.insertNth_apply_same]; exact sq_nonneg _
      · simpa only [Fin.insertNth_apply_succAbove] using add_nonneg (sq_nonneg (m j)) (hg0 i)
    · intro i
      rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨i, rfl⟩
      · simp only [Fin.insertNth_apply_same, Nat.cast_add, Nat.cast_one]
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sq_nonneg (m i))]
      · simp only [Fin.insertNth_apply_succAbove, Nat.cast_add, Nat.cast_one]
        have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
        simpa only [add_sub_cancel] using
          square_add_bound n (m j) (m (j.succAbove i) - m j) (g i) hn (hgl i)
    · intro i
      rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨i, rfl⟩
      · simp only [Fin.insertNth_apply_same, le_refl]
      · simp only [Fin.insertNth_apply_succAbove]
        nlinarith [hgu i, mul_nonneg (hm j)
          (sub_nonneg.mpr (hj (j.succAbove i) (Finset.mem_univ _)))]
    · intro i k
      rcases Fin.eq_self_or_eq_succAbove j i with hi | ⟨i, rfl⟩
      · subst i
        rcases Fin.eq_self_or_eq_succAbove j k with hk | ⟨k, rfl⟩
        · subst k; simp
        · simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
          nlinarith [hg0 k, sq_nonneg (m j - m (j.succAbove k))]
      · rcases Fin.eq_self_or_eq_succAbove j k with hk | ⟨k, rfl⟩
        · subst k
          simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
          nlinarith [hgu i]
        · simp only [Fin.insertNth_apply_succAbove]
          nlinarith [hgd i k]

end SSPRK
