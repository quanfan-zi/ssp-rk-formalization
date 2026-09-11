import SSPRK.PhaseTypeCountMoments
import Mathlib.Data.Nat.Choose.Sum

/-!
# All counting moments of phase-type absorption weights

Repeated Cauchy products of the Neumann series yield binomial coefficients and all
rising factorial counting moments, without any moment assumptions.
-/

open scoped BigOperators Matrix.Norms.Operator

namespace SSPRK.PhaseTypeData

variable {s : ℕ} (d : PhaseTypeData s)

theorem hasSum_binomial_matrix (k : ℕ) :
    HasSum (fun n : ℕ ↦ ((n + k).choose k : ℝ) • d.transition ^ n)
      (d.green ^ (k + 1)) := by
  induction k with
  | zero =>
    simpa [green, d.substochastic.inv_eq_tsum d.transient] using
      (d.substochastic.summable_pow d.transient).hasSum
  | succ k ih =>
    letI : NormedRing (Matrix (Fin s) (Fin s) ℝ) := Matrix.linftyOpNormedRing
    have h := d.substochastic.summable_pow d.transient
    have hc := hasSum_sum_range_mul_of_summable_norm ih.summable.norm h.norm
    have he (n : ℕ) :
        (∑ j ∈ Finset.range (n + 1), ((j + k).choose k : ℝ) • d.transition ^ j *
          d.transition ^ (n - j)) =
            ((n + (k + 1)).choose (k + 1) : ℝ) • d.transition ^ n := by
      calc
        _ = ∑ j ∈ Finset.range (n + 1), ((j + k).choose k : ℝ) • d.transition ^ n :=
          Finset.sum_congr rfl fun j hj ↦ by
            rw [smul_mul_assoc, ← pow_add,
              Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
        _ = _ := by
          rw [← Finset.sum_smul, ← Nat.cast_sum, Nat.sum_range_add_choose, Nat.add_assoc]
    have ht : HasSum (fun n : ℕ ↦ d.transition ^ n) d.green := by
      rw [green, d.substochastic.inv_eq_tsum d.transient]
      exact h.hasSum
    convert hc using 1
    · exact funext fun n ↦ (he n).symm
    · rw [pow_succ]
      congr 1
      · exact ih.tsum_eq.symm
      · exact ht.tsum_eq.symm

theorem hasSum_binomial_count_moment (k : ℕ) :
    HasSum (fun n : ℕ ↦ ((n + k).choose k : ℝ) * d.weight n)
      (dotProduct d.initial ((d.green ^ k).mulVec (fun _ ↦ 1))) := by
  have he : (d.green ^ (k + 1)).mulVec d.exit =
      (d.green ^ k).mulVec (fun _ ↦ 1) := by
    rw [pow_succ, ← Matrix.mulVec_mulVec, d.green_mulVec_exit]
  simpa only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, weight, he] using
    d.hasSum_pairing (d.hasSum_binomial_matrix k) d.exit

theorem hasSum_rising_count_moment (k : ℕ) :
    HasSum (fun n : ℕ ↦ d.weight n * ((n + 1).ascFactorial k : ℝ))
      ((k.factorial : ℝ) * dotProduct d.initial ((d.green ^ k).mulVec (fun _ ↦ 1))) := by
  simpa only [Nat.ascFactorial_eq_factorial_mul_choose, Nat.cast_mul,
    mul_comm, mul_left_comm, mul_assoc] using
      (d.hasSum_binomial_count_moment k).mul_left (k.factorial : ℝ)

theorem summable_rising_count_moment (k : ℕ) :
    Summable (fun n : ℕ ↦ d.weight n * ((n + 1).ascFactorial k : ℝ)) :=
  (d.hasSum_rising_count_moment k).summable

theorem rising_count_moment (k : ℕ) :
    (∑' n : ℕ, d.weight n * ((n + 1).ascFactorial k : ℝ)) =
      (k.factorial : ℝ) * dotProduct d.initial ((d.green ^ k).mulVec (fun _ ↦ 1)) :=
  (d.hasSum_rising_count_moment k).tsum_eq

theorem rising_count_coefficient_eq (n k : ℕ) :
    ((n + 1).ascFactorial k : ℝ) = (n + k).factorial / (n.factorial : ℝ) := by
  apply (eq_div_iff (by exact_mod_cast n.factorial_ne_zero)).2
  exact_mod_cast (Nat.mul_comm _ _).trans (Nat.factorial_mul_ascFactorial n k)

theorem hasSum_factorial_count_moment (k : ℕ) :
    HasSum (fun n : ℕ ↦ d.weight n * ((n + k).factorial / (n.factorial : ℝ)))
      ((k.factorial : ℝ) * dotProduct d.initial ((d.green ^ k).mulVec (fun _ ↦ 1))) := by
  simpa only [rising_count_coefficient_eq] using d.hasSum_rising_count_moment k

theorem summable_factorial_count_moment (k : ℕ) :
    Summable (fun n : ℕ ↦ d.weight n * ((n + k).factorial / (n.factorial : ℝ))) :=
  (d.hasSum_factorial_count_moment k).summable

theorem factorial_count_moment (k : ℕ) :
    (∑' n : ℕ, d.weight n * ((n + k).factorial / (n.factorial : ℝ))) =
      (k.factorial : ℝ) * dotProduct d.initial ((d.green ^ k).mulVec (fun _ ↦ 1)) :=
  (d.hasSum_factorial_count_moment k).tsum_eq

end SSPRK.PhaseTypeData
