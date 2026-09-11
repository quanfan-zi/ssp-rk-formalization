import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Order conditions for the repeated implicit midpoint rule

The coefficients are the family in equation (5.1) of V1.6.  This module
establishes only its first two classical Runge--Kutta order conditions.
-/

open scoped BigOperators

namespace SSPRK

noncomputable section

/-- The $s$-fold equal-step implicit-midpoint tableau from equation (5.1). -/
def midpointA (s : ℕ) : Matrix (Fin s) (Fin s) ℝ := fun i j ↦
  if j < i then 1 / (s : ℝ) else if i = j then 1 / (2 * (s : ℝ)) else 0

/-- The uniform output weights of the tableau in equation (5.1). -/
def midpointB (s : ℕ) : Fin s → ℝ := fun _ ↦ 1 / (s : ℝ)

def midpointOnes (s : ℕ) : Fin s → ℝ := fun _ ↦ 1

theorem midpointA_mulVec_ones {s : ℕ} (hs : 0 < s) (i : Fin s) :
    Matrix.mulVec (midpointA s) (midpointOnes s) i =
      (2 * (i : ℝ) + 1) / (2 * (s : ℝ)) := by
  classical
  simp [Matrix.mulVec, dotProduct, midpointA, midpointOnes, Finset.sum_ite]
  have hcard : (Finset.univ.filter fun j : Fin s ↦ j < i).card = i.val := by
    have hset : Finset.univ.filter (fun j : Fin s ↦ j < i) = Finset.Iio i := by
      ext j
      simp
    rw [hset, Fin.card_Iio]
  rw [hcard]
  have hsreal : (s : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hs)
  field_simp [hsreal]

theorem sum_two_fin_val_add_one (s : ℕ) :
    ∑ i : Fin s, (2 * (i : ℝ) + 1) = (s : ℝ) ^ 2 := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.cast_zero, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    have hterm : ∀ i : Fin s, 2 * ((i : ℝ) + 1) + 1 = (2 * (i : ℝ) + 1) + 2 := by
      intro i
      ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ih]
    simp
    ring

theorem midpoint_order_one {s : ℕ} (hs : 0 < s) :
    dotProduct (midpointB s) (midpointOnes s) = 1 := by
  have hsreal : (s : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hs)
  simp [dotProduct, midpointB, midpointOnes]
  field_simp [hsreal]

theorem midpoint_order_two {s : ℕ} (hs : 0 < s) :
    dotProduct (midpointB s) (Matrix.mulVec (midpointA s) (midpointOnes s)) = 1 / 2 := by
  have hsreal : (s : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hs)
  calc
    dotProduct (midpointB s) (Matrix.mulVec (midpointA s) (midpointOnes s)) =
        ∑ i : Fin s, (1 / (s : ℝ)) * ((2 * (i : ℝ) + 1) / (2 * (s : ℝ))) := by
      simp only [dotProduct, midpointB]
      congr with i
      rw [midpointA_mulVec_ones hs i]
    _ = ∑ i : Fin s, (1 / (2 * (s : ℝ) ^ 2)) * (2 * (i : ℝ) + 1) := by
      congr with i
      field_simp [hsreal]
    _ = (1 / (2 * (s : ℝ) ^ 2)) * ∑ i : Fin s, (2 * (i : ℝ) + 1) := by
      rw [Finset.mul_sum]
    _ = 1 / 2 := by
      rw [sum_two_fin_val_add_one]
      field_simp [hsreal]

end

end SSPRK
