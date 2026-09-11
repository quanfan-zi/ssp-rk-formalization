import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# Exact potential levels on an arithmetic progression

Adjacent difference bounds and equality at the top level force every potential value.
The resulting quadratic equalities allow only the next lower level or immediate absorption
from the first level.
-/

namespace SSPRK

theorem variance_potential_ordered_levels {n : ℕ} {a : ℝ}
    (m f : Fin (n + 1) → ℝ)
    (hm : ∀ k, m k = (k.val + 1 : ℝ) * a)
    (hu : ∀ k, f k ≤ m k ^ 2)
    (hd : ∀ j k, f j - f k ≤ (m j - m k) ^ 2)
    (ht : f (Fin.last n) = (n + 1 : ℝ) * a ^ 2) :
    ∀ k, f k = (k.val + 1 : ℝ) * a ^ 2 := by
  have hadj (k : Fin n) : f k.succ - f k.castSucc ≤ a ^ 2 := by
    have h := hd k.succ k.castSucc
    rw [hm, hm] at h
    simpa only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one,
      show ∀ x : ℝ, (x + 1 + 1) * a - (x + 1) * a = a by intro x; ring] using h
  have hub : ∀ k, f k ≤ (k.val + 1 : ℝ) * a ^ 2 := by
    intro k
    induction k using Fin.induction with
    | zero => simpa [hm] using hu 0
    | succ k ih =>
      have h := hadj k
      simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] at *
      linarith
  intro k
  induction k using Fin.reverseInduction with
  | last => simpa using ht
  | cast k ih =>
    have h := hadj k
    have h' := hub k.castSucc
    simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] at *
    linarith

theorem variance_potential_permuted_levels {n : ℕ} {a : ℝ}
    (m f : Fin (n + 1) → ℝ) (e : Fin (n + 1) ≃ Fin (n + 1))
    (hm : ∀ k, m (e k) = (k.val + 1 : ℝ) * a)
    (hu : ∀ k, f k ≤ m k ^ 2)
    (hd : ∀ j k, f j - f k ≤ (m j - m k) ^ 2)
    (ht : f (e (Fin.last n)) = (n + 1 : ℝ) * a ^ 2) :
    ∀ k, f (e k) = (k.val + 1 : ℝ) * a ^ 2 := by
  exact variance_potential_ordered_levels (fun k ↦ m (e k)) (fun k ↦ f (e k))
    hm (fun k ↦ hu (e k)) (fun j k ↦ hd (e j) (e k)) ht

theorem variance_potential_level_jump_eq {s : ℕ} {a : ℝ} (ha : 0 < a)
    (m f : Fin s → ℝ) (e : Fin s ≃ Fin s)
    (hm : ∀ k, m (e k) = (k.val + 1 : ℝ) * a)
    (hf : ∀ k, f (e k) = (k.val + 1 : ℝ) * a ^ 2)
    (j k : Fin s) (he : f (e j) - f (e k) = (m (e j) - m (e k)) ^ 2) :
    j = k ∨ j.val = k.val + 1 := by
  rw [hm, hm, hf, hf] at he
  have hp : ((j.val : ℝ) - k.val) * ((j.val : ℝ) - k.val - 1) * a ^ 2 = 0 := by
    nlinarith
  have hz := (mul_eq_zero.mp hp).resolve_right (ne_of_gt (sq_pos_of_pos ha))
  rcases mul_eq_zero.mp hz with h | h
  · left
    apply Fin.ext
    exact_mod_cast sub_eq_zero.mp h
  · right
    have h' : (j.val : ℝ) = k.val + 1 := by linarith
    exact_mod_cast h'

theorem variance_potential_level_absorb_eq {s : ℕ} {a : ℝ} (ha : 0 < a)
    (m f : Fin s → ℝ) (e : Fin s ≃ Fin s)
    (hm : ∀ k, m (e k) = (k.val + 1 : ℝ) * a)
    (hf : ∀ k, f (e k) = (k.val + 1 : ℝ) * a ^ 2)
    (j : Fin s) (he : f (e j) = m (e j) ^ 2) : j.val = 0 := by
  rw [hm, hf] at he
  have hp : (j.val : ℝ) * ((j.val : ℝ) + 1) * a ^ 2 = 0 := by nlinarith
  have hz := (mul_eq_zero.mp hp).resolve_right (ne_of_gt (sq_pos_of_pos ha))
  have hj := (mul_eq_zero.mp hz).resolve_right (by positivity)
  exact_mod_cast hj

end SSPRK
