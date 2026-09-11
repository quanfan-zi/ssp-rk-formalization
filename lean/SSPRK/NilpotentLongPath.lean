import SSPRK.NilpotentPaths
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Long paths order a nonnegative nilpotent matrix

A positive entry in power `s - 1` yields a Hamilton path. Nilpotence excludes repeated
vertices and every backward support edge, so the path is an ordering of all states.
-/

open scoped BigOperators

namespace SSPRK

/-- Concatenating two positive power entries gives a positive entry at the sum of their lengths. -/
lemma positive_power_concat {s : ℕ} (P : Matrix (Fin s) (Fin s) ℝ)
    (hP : MatrixNonneg P) {a b : ℕ} {i j k : Fin s}
    (ha : 0 < (P ^ a) i j) (hb : 0 < (P ^ b) j k) :
    0 < (P ^ (a + b)) i k := by
  rw [pow_add, Matrix.mul_apply]
  exact (mul_pos ha hb).trans_le (Finset.single_le_sum
    (fun l _ ↦ mul_nonneg (matrix_pow_nonneg P hP a i l) (matrix_pow_nonneg P hP b l k))
    (Finset.mem_univ j))

/-- Every positive power of a nonnegative nilpotent matrix has a zero diagonal. -/
lemma nilpotent_power_diag_eq_zero {s : ℕ} (P : Matrix (Fin s) (Fin s) ℝ)
    (hP : MatrixNonneg P) (hnil : IsNilpotent P) (n : ℕ) (hn : 0 < n) (i : Fin s) :
    (P ^ n) i i = 0 := by
  have ht : Matrix.trace (P ^ n) = 0 :=
    (Matrix.isNilpotent_trace_of_isNilpotent (hnil.pow_of_pos hn.ne')).eq_zero
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ ↦ matrix_pow_nonneg P hP n j j)).mp ht i (Finset.mem_univ i)

/-- A positive power entry has a walk with a positive power entry along every forward subsegment. -/
theorem positive_power_walk {s : ℕ} (P : Matrix (Fin s) (Fin s) ℝ)
    (hP : MatrixNonneg P) (n : ℕ) {i j : Fin s} (hij : 0 < (P ^ n) i j) :
    ∃ f : ℕ → Fin s, f 0 = i ∧ f n = j ∧
      ∀ a b : ℕ, a ≤ b → b ≤ n → 0 < (P ^ (b - a)) (f a) (f b) := by
  induction n generalizing i j with
  | zero =>
    have heq : i = j := by
      by_contra h
      simp [h] at hij
    refine ⟨fun _ ↦ i, rfl, heq, ?_⟩
    intro a b hab hb
    have ha : a = 0 := by omega
    have hb' : b = 0 := by omega
    simp [ha, hb']
  | succ n ih =>
    obtain ⟨k, hik, hkj⟩ := exists_positive_power_factor P hP hij
    obtain ⟨f, hf0, hfn, hseg⟩ := ih hik
    refine ⟨fun l ↦ if l = n + 1 then j else f l, ?_, by simp, ?_⟩
    · simpa using hf0
    · intro a b hab hb
      by_cases hb' : b = n + 1
      · subst b
        by_cases ha : a = n + 1
        · subst a
          simp
        · have han : a ≤ n := by omega
          have hp := positive_power_concat P hP (hseg a n han le_rfl)
            (show 0 < (P ^ 1) (f n) j by simpa [hfn, PositiveEdge] using hkj)
          have hexp : n - a + 1 = n + 1 - a := by omega
          simpa only [ha, if_false, if_true, hexp] using hp
      · have hbn : b ≤ n := by omega
        have ha : a ≠ n + 1 := by omega
        simpa only [ha, hb', if_false] using hseg a b hab hbn

/-- A positive walk in a nonnegative nilpotent matrix never repeats a vertex. -/
theorem positive_power_walk_injective {s n : ℕ} (P : Matrix (Fin s) (Fin s) ℝ)
    (hP : MatrixNonneg P) (hnil : IsNilpotent P) (f : ℕ → Fin s)
    (hseg : ∀ a b : ℕ, a ≤ b → b ≤ n → 0 < (P ^ (b - a)) (f a) (f b)) :
    Function.Injective (fun a : Fin (n + 1) ↦ f a.val) := by
  have hne (a b : Fin (n + 1)) (hab : a < b) : f a.val ≠ f b.val := by
    intro heq
    have hp := hseg a.val b.val (Nat.le_of_lt hab) (Nat.le_of_lt_succ b.isLt)
    rw [heq, nilpotent_power_diag_eq_zero P hP hnil _ (Nat.sub_pos_of_lt hab)] at hp
    exact lt_irrefl 0 hp
  intro a b hab
  rcases lt_trichotomy a b with h | h | h
  · exact False.elim (hne a b h hab)
  · exact h
  · exact False.elim (hne b a h hab.symm)

/-- A support edge between vertices of a positive nilpotent walk must go strictly forward. -/
theorem positive_power_walk_edge_forward {s n : ℕ} (P : Matrix (Fin s) (Fin s) ℝ)
    (hP : MatrixNonneg P) (hnil : IsNilpotent P) (f : ℕ → Fin s)
    (hseg : ∀ a b : ℕ, a ≤ b → b ≤ n → 0 < (P ^ (b - a)) (f a) (f b))
    (a b : Fin (n + 1)) (hEdge : 0 < P (f a.val) (f b.val)) : a < b := by
  by_contra h
  have hba : b.val ≤ a.val := le_of_not_gt h
  have hp := positive_power_concat P hP
    (hseg b.val a.val hba (Nat.le_of_lt_succ a.isLt))
    (show 0 < (P ^ 1) (f a.val) (f b.val) by simpa using hEdge)
  rw [nilpotent_power_diag_eq_zero P hP hnil _ (by omega)] at hp
  exact lt_irrefl 0 hp

/-- A maximal-length positive nilpotent path orders all states from its initial to final vertex. -/
theorem nilpotent_long_path_order {n : ℕ}
    (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hP : MatrixNonneg P)
    (hnil : P ^ (n + 1) = 0) {i j : Fin (n + 1)} (hlong : 0 < (P ^ n) i j) :
    ∃ e : Fin (n + 1) ≃ Fin (n + 1), e 0 = i ∧ e (Fin.last n) = j ∧
      (∀ a b : Fin (n + 1), b.val = a.val + 1 → 0 < P (e a) (e b)) ∧
      ∀ a b : Fin (n + 1), 0 < P (e a) (e b) → a < b := by
  obtain ⟨f, hf0, hfn, hseg⟩ := positive_power_walk P hP n hlong
  have hnil' : IsNilpotent P := ⟨n + 1, hnil⟩
  have hinj := positive_power_walk_injective P hP hnil' f hseg
  let e : Fin (n + 1) ≃ Fin (n + 1) :=
    Equiv.ofBijective (fun a ↦ f a.val) ⟨hinj, Finite.surjective_of_injective hinj⟩
  refine ⟨e, hf0, hfn, ?_, ?_⟩
  · intro a b hab
    have hp := hseg a.val b.val (by omega) (Nat.le_of_lt_succ b.isLt)
    have hdiff : b.val - a.val = 1 := by omega
    simpa only [hdiff, pow_one] using hp
  · intro a b hab
    exact positive_power_walk_edge_forward P hP hnil' f hseg a b hab

/-- The long-path ordering stated for any positive matrix size. -/
theorem nilpotent_long_path_order_of_pos {s : ℕ} (hs : 0 < s)
    (P : Matrix (Fin s) (Fin s) ℝ) (hP : MatrixNonneg P)
    (hnil : P ^ s = 0) {i j : Fin s} (hlong : 0 < (P ^ (s - 1)) i j) :
    ∃ e : Fin s ≃ Fin s, e ⟨0, hs⟩ = i ∧ e ⟨s - 1, by omega⟩ = j ∧
      (∀ a b : Fin s, b.val = a.val + 1 → 0 < P (e a) (e b)) ∧
      ∀ a b : Fin s, 0 < P (e a) (e b) → a < b := by
  cases s with
  | zero => omega
  | succ n => exact nilpotent_long_path_order P hP hnil hlong

end SSPRK
