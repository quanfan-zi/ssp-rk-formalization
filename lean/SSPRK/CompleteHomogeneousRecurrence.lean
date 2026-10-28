import SSPRK.CompleteHomogeneousRaising

/-!
# Recurrence in one variable for complete homogeneous polynomials

Separate weak compositions according to whether their first coordinate vanishes.
This gives the usual recursion used by the finite acyclic-path expansion.
-/

open scoped BigOperators

namespace SSPRK

@[simp] theorem completeHomogeneous_empty (θ : Fin 0 → ℝ) (k : ℕ) :
    completeHomogeneous θ k = if k = 0 then 1 else 0 := by
  cases k <;> simp [completeHomogeneous, Finset.Nat.antidiagonalTuple_zero_right,
    compositionMonomial]

theorem compositionMonomial_cons {s : ℕ} (c : ℝ) (θ : Fin s → ℝ) (n : ℕ)
    (a : Fin s → ℕ) :
    compositionMonomial (Fin.cons c θ) (Fin.cons n a) = c ^ n * compositionMonomial θ a := by
  simp [compositionMonomial, Fin.prod_univ_succ]

private theorem completeHomogeneous_head_zero {s : ℕ} (c : ℝ) (θ : Fin s → ℝ) (k : ℕ) :
    completeHomogeneous θ k =
      ∑ b ∈ (Finset.Nat.antidiagonalTuple (s + 1) k).filter (fun b ↦ b 0 = 0),
        compositionMonomial (Fin.cons c θ) b := by
  classical
  unfold completeHomogeneous
  refine Finset.sum_bij (fun a _ ↦ Fin.cons 0 a) ?_ ?_ ?_ ?_
  · intro a ha
    simpa [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] using
      Finset.Nat.mem_antidiagonalTuple.mp ha
  · intro a ha b hb hab
    exact Fin.cons_right_injective 0 hab
  · intro b hb
    obtain ⟨hdegree, hzero⟩ := Finset.mem_filter.mp hb
    refine ⟨Fin.tail b, ?_, ?_⟩
    · apply Finset.Nat.mem_antidiagonalTuple.mpr
      have h := Finset.Nat.mem_antidiagonalTuple.mp hdegree
      simpa [Fin.sum_univ_succ, hzero, Fin.tail] using h
    · simpa [hzero] using Fin.cons_self_tail b
  · intro a ha
    simp [compositionMonomial_cons]

private lemma update_zero_sum_succ {s : ℕ} (a : Fin (s + 1) → ℕ) :
    (∑ j, Function.update a 0 (a 0 + 1) j) = (∑ j, a j) + 1 := by
  simp [Fin.sum_univ_succ, add_assoc, add_comm]

private theorem completeHomogeneous_head_nonzero {s : ℕ} (c : ℝ) (θ : Fin s → ℝ)
    (k : ℕ) :
    c * completeHomogeneous (Fin.cons c θ) k =
      ∑ b ∈ (Finset.Nat.antidiagonalTuple (s + 1) (k + 1)).filter (fun b ↦ b 0 ≠ 0),
        compositionMonomial (Fin.cons c θ) b := by
  classical
  rw [completeHomogeneous, Finset.mul_sum]
  refine Finset.sum_bij (fun a _ ↦ Function.update a 0 (a 0 + 1)) ?_ ?_ ?_ ?_
  · intro a ha
    apply Finset.mem_filter.mpr
    constructor
    · simp only [Finset.Nat.mem_antidiagonalTuple, update_zero_sum_succ,
        Finset.Nat.mem_antidiagonalTuple.mp ha]
    · simp
  · intro a ha b hb hab
    ext j
    by_cases hj : j = 0
    · subst j
      have h := congrFun hab 0
      simpa using h
    · have h := congrFun hab j
      simpa [hj] using h
  · intro b hb
    have hbi : 1 ≤ b 0 := Nat.one_le_iff_ne_zero.mpr (Finset.mem_filter.mp hb).2
    let a := Function.update b 0 (b 0 - 1)
    have hrecover : Function.update a 0 (a 0 + 1) = b := by
      simp [a, Nat.sub_add_cancel hbi]
    have ha : a ∈ Finset.Nat.antidiagonalTuple (s + 1) k := by
      apply Finset.Nat.mem_antidiagonalTuple.mpr
      have hsum := update_zero_sum_succ a
      rw [hrecover, Finset.Nat.mem_antidiagonalTuple.mp (Finset.mem_filter.mp hb).1] at hsum
      omega
    exact ⟨a, ha, hrecover⟩
  · intro a ha
    simp [compositionMonomial_update_succ, mul_comm]

/-- The standard recurrence after adjoining one variable. -/
theorem completeHomogeneous_cons_succ {s : ℕ} (c : ℝ) (θ : Fin s → ℝ) (k : ℕ) :
    completeHomogeneous (Fin.cons c θ) (k + 1) =
      c * completeHomogeneous (Fin.cons c θ) k + completeHomogeneous θ (k + 1) := by
  classical
  rw [completeHomogeneous_head_nonzero, completeHomogeneous_head_zero c θ]
  exact (Finset.sum_filter_not_add_sum_filter
    (Finset.Nat.antidiagonalTuple (s + 1) (k + 1)) (fun b ↦ b 0 = 0)
    (compositionMonomial (Fin.cons c θ))).symm

@[simp] theorem completeHomogeneous_zero_cons {s : ℕ} (θ : Fin s → ℝ) (k : ℕ) :
    completeHomogeneous (Fin.cons 0 θ) k = completeHomogeneous θ k := by
  cases k with
  | zero => simp
  | succ k => simp [completeHomogeneous_cons_succ]

end SSPRK
