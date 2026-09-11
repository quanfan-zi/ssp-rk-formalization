import SSPRK.NilpotentPaths
import SSPRK.ChainMatrices

/-!
# Rigidity of an ordered substochastic chain

A forward chain with positive occupation of every state and maximal expected length must
start at the first state and visit each successive state with probability one.
-/

open scoped BigOperators

namespace SSPRK

/-- The number of available positions starting at an ordered state. -/
def orderedRank {s : ℕ} (i : Fin s) : ℝ := (s : ℝ) - i.val

lemma orderedRank_sub_one_nonneg {s : ℕ} (i : Fin s) : 0 ≤ orderedRank i - 1 := by
  have hi : (i.val : ℝ) + 1 ≤ s := by exact_mod_cast i.isLt
  dsimp [orderedRank]
  linarith

/-- A forward substochastic row loses at least one unit of rank. -/
lemma ordered_rank_row_le {s : ℕ} (P : Matrix (Fin s) (Fin s) ℝ)
    (hP : MatrixNonneg P) (hrow : ∀ i, ∑ j, P i j ≤ 1)
    (hforward : ∀ i j, 0 < P i j → i < j) (i : Fin s) :
    ∑ j, P i j * orderedRank j ≤ orderedRank i - 1 := by
  calc
    ∑ j, P i j * orderedRank j ≤ ∑ j, P i j * (orderedRank i - 1) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hp : P i j = 0
      · simp [hp]
      · have hij := hforward i j (lt_of_le_of_ne (hP i j) (Ne.symm hp))
        have hij' : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hij
        exact mul_le_mul_of_nonneg_left (by dsimp [orderedRank]; linarith) (hP i j)
    _ = (∑ j, P i j) * (orderedRank i - 1) := (Finset.sum_mul ..).symm
    _ ≤ orderedRank i - 1 := by
      simpa using mul_le_mul_of_nonneg_right (hrow i) (orderedRank_sub_one_nonneg i)

/-- The occupation balance telescopes against any test vector. -/
lemma occupation_balance_pairing {s : ℕ} (P : Matrix (Fin s) (Fin s) ℝ)
    (π q r : Fin s → ℝ) (hbalance : ∀ j, q j = π j + ∑ i, q i * P i j) :
    ∑ i, q i * (r i - ∑ j, P i j * r j) = ∑ i, π i * r i := by
  simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i j ↦ q i * (P i j * r j))]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [hbalance i]
  ring

/-- Maximal occupation forces equality in every ordered rank loss. -/
theorem ordered_rank_eq_of_maximal_occupation {s : ℕ}
    (P : Matrix (Fin s) (Fin s) ℝ) (π q : Fin s → ℝ)
    (hP : MatrixNonneg P) (hrow : ∀ i, ∑ j, P i j ≤ 1)
    (hforward : ∀ i j, 0 < P i j → i < j)
    (hπ : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i = 1)
    (hq : ∀ i, 0 < q i) (hqsum : ∑ i, q i = s)
    (hbalance : ∀ j, q j = π j + ∑ i, q i * P i j) :
    (∀ i, ∑ j, P i j * orderedRank j = orderedRank i - 1) ∧
      ∑ i, π i * orderedRank i = s := by
  have hrank : ∑ i, π i * orderedRank i ≤ s := by
    calc
      _ ≤ ∑ i, π i * (s : ℝ) := Finset.sum_le_sum fun i _ ↦
        mul_le_mul_of_nonneg_left (sub_le_self _ (Nat.cast_nonneg _)) (hπ i)
      _ = s := by rw [← Finset.sum_mul, hπsum, one_mul]
  have hdef (i : Fin s) : 0 ≤ q i *
      (orderedRank i - 1 - ∑ j, P i j * orderedRank j) :=
    mul_nonneg (hq i).le (sub_nonneg.mpr (ordered_rank_row_le P hP hrow hforward i))
  have hsum : (∑ i, q i * (orderedRank i - 1 - ∑ j, P i j * orderedRank j)) =
      (∑ i, π i * orderedRank i) - s := by
    have ht := occupation_balance_pairing P π q orderedRank hbalance
    simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib] at ht ⊢
    rw [hqsum]
    linarith
  have hz : (∑ i, q i * (orderedRank i - 1 - ∑ j, P i j * orderedRank j)) = 0 :=
    le_antisymm (by rw [hsum]; linarith) (Finset.sum_nonneg fun i _ ↦ hdef i)
  refine ⟨?_, by linarith⟩
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ hdef i)).mp hz i
    (Finset.mem_univ i)
  have hi' := (mul_eq_zero.mp hi).resolve_left (hq i).ne'
  linarith

/-- An initial distribution with maximal rank is concentrated at the first position. -/
lemma initial_eq_first_of_rank_eq {s : ℕ} (π : Fin s → ℝ)
    (hπ : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i = 1)
    (hrank : ∑ i, π i * orderedRank i = s) (i : Fin s) :
    π i = if i.val = 0 then 1 else 0 := by
  have hz : ∑ j, π j * (j.val : ℝ) = 0 := by
    simp only [orderedRank, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hπsum, one_mul] at hrank
    linarith
  have hzero (j : Fin s) (hj : j.val ≠ 0) : π j = 0 := by
    have hjz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ ↦ mul_nonneg (hπ j) (Nat.cast_nonneg _))).mp hz j (Finset.mem_univ j)
    exact (mul_eq_zero.mp hjz).resolve_right (by exact_mod_cast hj)
  split_ifs with hi
  · have hs : ∑ j, π j = π i := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact hzero j (by intro hj; apply hji; exact Fin.ext (hj.trans hi.symm))
      · simp
    linarith
  · exact hzero i hi

/-- Equality in the rank bound excludes all transitions except the immediate successor. -/
lemma ordered_rank_eq_support {s : ℕ} (P : Matrix (Fin s) (Fin s) ℝ)
    (hP : MatrixNonneg P) (hrow : ∀ i, ∑ j, P i j ≤ 1)
    (hforward : ∀ i j, 0 < P i j → i < j)
    (heq : ∀ i, ∑ j, P i j * orderedRank j = orderedRank i - 1)
    (i j : Fin s) (hij : j.val ≠ i.val + 1) : P i j = 0 := by
  have hn (k : Fin s) : 0 ≤ P i k * (orderedRank i - 1 - orderedRank k) := by
    by_cases hp : P i k = 0
    · simp [hp]
    · have hik : (i.val : ℝ) + 1 ≤ k.val := by
        exact_mod_cast hforward i k (lt_of_le_of_ne (hP i k) (Ne.symm hp))
      exact mul_nonneg (hP i k) (by dsimp [orderedRank]; linarith)
  have hs : ∑ k, P i k * (orderedRank i - 1 - orderedRank k) = 0 := by
    apply le_antisymm
    · simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      rw [heq i]
      have hb := mul_le_mul_of_nonneg_right (hrow i) (orderedRank_sub_one_nonneg i)
      linarith
    · exact Finset.sum_nonneg fun k _ ↦ hn k
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ ↦ hn k)).mp hs j
    (Finset.mem_univ j)
  apply (mul_eq_zero.mp hj).resolve_right
  intro hr
  apply hij
  have hr' : (j.val : ℝ) = i.val + 1 := by dsimp [orderedRank] at hr; linarith
  exact_mod_cast hr'

/-- Equality in every ordered rank loss characterizes the deterministic successor matrix. -/
theorem ordered_matrix_eq_successor {s : ℕ} (P : Matrix (Fin s) (Fin s) ℝ)
    (hP : MatrixNonneg P) (hrow : ∀ i, ∑ j, P i j ≤ 1)
    (hforward : ∀ i j, 0 < P i j → i < j)
    (heq : ∀ i, ∑ j, P i j * orderedRank j = orderedRank i - 1)
    (i j : Fin s) : P i j = if j.val = i.val + 1 then 1 else 0 := by
  split_ifs with hij
  · have hs : ∑ k, P i k * orderedRank k = P i j * orderedRank j := by
      apply Finset.sum_eq_single j
      · intro k _ hkj
        rw [ordered_rank_eq_support P hP hrow hforward heq i k
          (by intro hk; apply hkj; exact Fin.ext (hk.trans hij.symm)), zero_mul]
      · simp
    have hj : 0 < orderedRank j := by
      have hj' : (j.val : ℝ) < s := by exact_mod_cast j.isLt
      exact sub_pos.mpr hj'
    have hr : orderedRank i - 1 = orderedRank j := by
      have hij' : (j.val : ℝ) = i.val + 1 := by exact_mod_cast hij
      dsimp [orderedRank]
      linarith
    rw [heq i, hr] at hs
    nlinarith
  · exact ordered_rank_eq_support P hP hrow hforward heq i j hij

/-- A positive initial first state and positive successor edges give positive occupation. -/
theorem occupation_pos_of_adjacent {s : ℕ} (P : Matrix (Fin s) (Fin s) ℝ)
    (π q : Fin s → ℝ) (hP : MatrixNonneg P)
    (hπ : ∀ i, 0 ≤ π i) (hq : ∀ i, 0 ≤ q i)
    (hfirst : ∀ i : Fin s, i.val = 0 → 0 < π i)
    (hadj : ∀ i j : Fin s, j.val = i.val + 1 → 0 < P i j)
    (hbalance : ∀ j, q j = π j + ∑ i, q i * P i j) : ∀ j, 0 < q j := by
  have hpos : ∀ n : ℕ, ∀ j : Fin s, j.val = n → 0 < q j := by
    intro n
    induction n with
    | zero =>
      intro j hj
      rw [hbalance j]
      exact add_pos_of_pos_of_nonneg (hfirst j hj)
        (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hq i) (hP i j))
    | succ n ih =>
      intro j hj
      let i : Fin s := ⟨n, by omega⟩
      have hip : 0 < q i := ih i rfl
      have hp : 0 < P i j := hadj i j (by simpa [i] using hj)
      have hsum : 0 < ∑ k, q k * P k j := (mul_pos hip hp).trans_le
        (Finset.single_le_sum (fun k _ ↦ mul_nonneg (hq k) (hP k j))
          (Finset.mem_univ i))
      rw [hbalance j]
      exact add_pos_of_nonneg_of_pos (hπ j) hsum
  exact fun j ↦ hpos j.val j rfl

/-- Maximal expected length forces a forward chain to traverse every state deterministically. -/
theorem ordered_chain_of_maximal_occupation {s : ℕ}
    (P : Matrix (Fin s) (Fin s) ℝ) (π q : Fin s → ℝ)
    (hP : MatrixNonneg P) (hrow : ∀ i, ∑ j, P i j ≤ 1)
    (hforward : ∀ i j, 0 < P i j → i < j)
    (hπ : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i = 1)
    (hq : ∀ i, 0 < q i) (hqsum : ∑ i, q i = s)
    (hbalance : ∀ j, q j = π j + ∑ i, q i * P i j) :
    (∀ i, π i = if i.val = 0 then 1 else 0) ∧
      ∀ i j, P i j = if j.val = i.val + 1 then 1 else 0 := by
  obtain ⟨hr, hπr⟩ := ordered_rank_eq_of_maximal_occupation
    P π q hP hrow hforward hπ hπsum hq hqsum hbalance
  exact ⟨initial_eq_first_of_rank_eq π hπ hπsum hπr,
    ordered_matrix_eq_successor P hP hrow hforward hr⟩

/-- Reversing the deterministic successor order gives the usual downward shift matrix. -/
theorem successor_reverse_eq_shiftDown {s : ℕ} (P : Matrix (Fin s) (Fin s) ℝ)
    (hP : ∀ i j, P i j = if j.val = i.val + 1 then 1 else 0) :
    (fun i j : Fin s ↦ P i.rev j.rev) = shiftDown s := by
  funext i j
  rw [hP]
  have hrev : j.rev.val = i.rev.val + 1 ↔ i.val = j.val + 1 := by
    simp only [Fin.rev]
    omega
  simp only [shiftDown, hrev]

end SSPRK
