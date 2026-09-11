import SSPRK.VariancePotential
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Option
import Mathlib.Tactic

/-!
# Equality in the finite variance potential bound

The minimum-coordinate construction can be chosen so that equality at a positive
coordinate forces all coordinate levels to form a strictly positive arithmetic progression.
-/

namespace SSPRK

private lemma square_add_eq_conditions (n a u v : ℝ) (hn : 0 < n)
    (h : u ^ 2 ≤ n * v) (he : (a + u) ^ 2 = (n + 1) * (a ^ 2 + v)) :
    u = n * a ∧ u ^ 2 = n * v := by
  have hc : (n + 1) * (n * v - u ^ 2) + (u - n * a) ^ 2 = 0 := by
    nlinarith [show n * ((n + 1) * (a ^ 2 + v) - (a + u) ^ 2) =
      (n + 1) * (n * v - u ^ 2) + (u - n * a) ^ 2 by ring]
  have hp : 0 ≤ (n + 1) * (n * v - u ^ 2) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr h)
  have hz : (u - n * a) ^ 2 = 0 := by nlinarith [sq_nonneg (u - n * a)]
  refine ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp hz), ?_⟩
  have : (n + 1) * (n * v - u ^ 2) = 0 := by linarith
  have := (mul_eq_zero.mp this).resolve_left (by linarith)
  linarith


private lemma square_add_bound (n a u v : ℝ) (hn : 0 < n) (h : u ^ 2 ≤ n * v) :
    (a + u) ^ 2 ≤ (n + 1) * (a ^ 2 + v) := by
  have hc : n * ((n + 1) * (a ^ 2 + v) - (a + u) ^ 2) =
      (n + 1) * (n * v - u ^ 2) + (u - n * a) ^ 2 := by ring
  have hnonneg : 0 ≤ n * ((n + 1) * (a ^ 2 + v) - (a + u) ^ 2) := by
    rw [hc]
    exact add_nonneg (mul_nonneg (by linarith) (sub_nonneg.mpr h)) (sq_nonneg _)
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hnonneg hn)

/-- Nonnegative coordinates admit a potential controlled by their squared differences. -/
theorem exists_variance_potential_with_equality (s : ℕ) (m : Fin s → ℝ) (hm : ∀ i, 0 ≤ m i) :
    ∃ f : Fin s → ℝ, (∀ i, 0 ≤ f i) ∧ (∀ i, m i ^ 2 ≤ (s : ℝ) * f i) ∧
      (∀ i, f i ≤ m i ^ 2) ∧ (∀ i j, f i - f j ≤ (m i - m j) ^ 2) ∧
      (∀ i, 0 < m i → m i ^ 2 = (s : ℝ) * f i →
        ∃ e : Fin s ≃ Fin s, ∀ k, m (e k) = (k.val + 1 : ℝ) * m i / s) := by
  induction s with
  | zero => exact ⟨fun _ ↦ 0, by simp, by simp, by simp, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ m Finset.univ_nonempty
    obtain ⟨g, hg0, hgl, hgu, hgd, hge⟩ := ih (fun i ↦ m (j.succAbove i) - m j)
      (fun i ↦ sub_nonneg.mpr (hj _ (Finset.mem_univ _)))
    refine ⟨j.insertNth (m j ^ 2) (fun i ↦ m j ^ 2 + g i), ?_, ?_, ?_, ?_, ?_⟩
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

    · intro i hi he
      rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨i, rfl⟩
      · simp only [Fin.insertNth_apply_same, Nat.cast_add, Nat.cast_one] at he
        have hn : n = 0 := by
          have : (n : ℝ) = 0 := by nlinarith [sq_pos_of_pos hi]
          exact_mod_cast this
        subst n
        refine ⟨Equiv.refl _, ?_⟩
        intro k
        have hk : k = i := by apply Fin.ext; omega
        subst k
        simp
      · simp only [Fin.insertNth_apply_succAbove, Nat.cast_add, Nat.cast_one] at he
        have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
        have he' : (m j + (m (j.succAbove i) - m j)) ^ 2 =
            ((n : ℝ) + 1) * (m j ^ 2 + g i) := by simpa only [add_sub_cancel] using he
        obtain ⟨hu, hv⟩ := square_add_eq_conditions n (m j)
          (m (j.succAbove i) - m j) (g i) hn (hgl i) he'
        have ha : 0 < m j := by nlinarith
        have hp : 0 < m (j.succAbove i) - m j := by rw [hu]; positivity
        obtain ⟨e, he⟩ := hge i hp hv
        refine ⟨(finSuccEquiv n).trans ((Equiv.optionCongr e).trans
          (finSuccEquiv' j).symm), ?_⟩
        intro k
        refine Fin.cases ?_ (fun r ↦ ?_) k
        · simp only [Equiv.trans_apply, finSuccEquiv_zero, Equiv.optionCongr_apply,
            Option.map_none, finSuccEquiv'_symm_none, Fin.val_zero,
            Nat.cast_zero, zero_add, one_mul, Nat.cast_add, Nat.cast_one]
          apply (eq_div_iff (by positivity : (n : ℝ) + 1 ≠ 0)).2
          nlinarith
        · simp only [Equiv.trans_apply, finSuccEquiv_succ, Equiv.optionCongr_apply,
            Option.map_some, finSuccEquiv'_symm_some, Fin.val_succ, Nat.cast_add,
            Nat.cast_one]
          have hr := he r
          rw [hu] at hr
          have hr' : m (j.succAbove (e r)) - m j = (r.val + 1 : ℝ) * m j := by
            convert hr using 1
            field_simp
          have hmi : m (j.succAbove i) = ((n : ℝ) + 1) * m j := by linarith
          have hmr : m (j.succAbove (e r)) = (r.val + 1 + 1 : ℝ) * m j := by
            linarith
          rw [hmr, hmi]
          field_simp

end SSPRK
