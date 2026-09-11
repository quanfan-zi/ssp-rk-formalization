import SSPRK.PhaseTypeWeights
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Counting moments of phase-type absorption weights

The Cauchy products of two and three Neumann series give the first two rising
factorial counting moments, together with their summability.
-/

open scoped BigOperators Matrix.Norms.Operator

namespace SSPRK.PhaseTypeData

variable {s : ℕ} (d : PhaseTypeData s)

theorem hasSum_first_matrix :
    HasSum (fun n : ℕ ↦ (n + 1 : ℝ) • d.transition ^ n) (d.green ^ 2) := by
  letI : NormedRing (Matrix (Fin s) (Fin s) ℝ) := Matrix.linftyOpNormedRing
  have h := d.substochastic.summable_pow d.transient
  have hc := hasSum_sum_range_mul_of_summable_norm h.norm h.norm
  have he (n : ℕ) :
      (∑ k ∈ Finset.range (n + 1), d.transition ^ k * d.transition ^ (n - k)) =
        (n + 1 : ℝ) • d.transition ^ n := by
    calc
      _ = ∑ _k ∈ Finset.range (n + 1), d.transition ^ n :=
        Finset.sum_congr rfl fun k hk ↦ by
          rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
      _ = _ := by simp [← Nat.cast_smul_eq_nsmul ℝ]
  have ht : HasSum (fun n : ℕ ↦ d.transition ^ n) d.green := by
    rw [green, d.substochastic.inv_eq_tsum d.transient]
    exact h.hasSum
  convert hc using 1
  · exact funext fun n ↦ (he n).symm
  · rw [pow_two]
    congr 1 <;> exact ht.tsum_eq.symm

theorem hasSum_first_count_moment :
    HasSum (fun n : ℕ ↦ (n + 1 : ℝ) * d.weight n)
      (dotProduct d.initial (d.green.mulVec (fun _ ↦ 1))) := by
  have h := d.hasSum_pairing d.hasSum_first_matrix d.exit
  simpa only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, weight,
    pow_two, ← Matrix.mulVec_mulVec, d.green_mulVec_exit] using h

theorem summable_first_count_moment :
    Summable (fun n : ℕ ↦ (n + 1 : ℝ) * d.weight n) :=
  d.hasSum_first_count_moment.summable

theorem first_count_moment :
    (∑' n : ℕ, (n + 1 : ℝ) * d.weight n) =
      dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)) :=
  d.hasSum_first_count_moment.tsum_eq

private theorem sum_count_coeff (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (k + 1 : ℝ)) = (n + 1 : ℝ) * (n + 2) / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem hasSum_half_second_matrix :
    HasSum (fun n : ℕ ↦ ((n + 1 : ℝ) * (n + 2) / 2) • d.transition ^ n)
      (d.green ^ 3) := by
  letI : NormedRing (Matrix (Fin s) (Fin s) ℝ) := Matrix.linftyOpNormedRing
  have h := d.substochastic.summable_pow d.transient
  have h₁ := d.hasSum_first_matrix
  have hc := hasSum_sum_range_mul_of_summable_norm h₁.summable.norm h.norm
  have he (n : ℕ) :
      (∑ k ∈ Finset.range (n + 1), (k + 1 : ℝ) • d.transition ^ k *
        d.transition ^ (n - k)) = ((n + 1 : ℝ) * (n + 2) / 2) • d.transition ^ n := by
    calc
      _ = ∑ k ∈ Finset.range (n + 1), (k + 1 : ℝ) • d.transition ^ n :=
        Finset.sum_congr rfl fun k hk ↦ by
          rw [smul_mul_assoc, ← pow_add,
            Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
      _ = _ := by rw [← Finset.sum_smul, sum_count_coeff]
  have ht : HasSum (fun n : ℕ ↦ d.transition ^ n) d.green := by
    rw [green, d.substochastic.inv_eq_tsum d.transient]
    exact h.hasSum
  convert hc using 1
  · exact funext fun n ↦ (he n).symm
  · rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ]
    congr 1
    · exact h₁.tsum_eq.symm
    · exact ht.tsum_eq.symm

theorem hasSum_second_count_moment :
    HasSum (fun n : ℕ ↦ (n + 1 : ℝ) * (n + 2) * d.weight n)
      (2 * dotProduct d.initial ((d.green ^ 2).mulVec (fun _ ↦ 1))) := by
  have h := d.hasSum_pairing d.hasSum_half_second_matrix d.exit
  simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    show (3 : ℕ) = 2 + 1 from rfl, pow_succ, ← Matrix.mulVec_mulVec,
    d.green_mulVec_exit] at h
  have h₂ := h.mul_left 2
  convert h₂ using 1
  · funext n
    unfold weight
    ring
  · simp only [pow_zero, Matrix.mulVec_mulVec, pow_two, Matrix.one_mul]

theorem summable_second_count_moment :
    Summable (fun n : ℕ ↦ (n + 1 : ℝ) * (n + 2) * d.weight n) :=
  d.hasSum_second_count_moment.summable

theorem second_count_moment :
    (∑' n : ℕ, (n + 1 : ℝ) * (n + 2) * d.weight n) =
      2 * dotProduct d.initial ((d.green ^ 2).mulVec (fun _ ↦ 1)) :=
  d.hasSum_second_count_moment.tsum_eq

end SSPRK.PhaseTypeData
