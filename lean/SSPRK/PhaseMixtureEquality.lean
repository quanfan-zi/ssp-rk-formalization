import SSPRK.SecondOrderEquality

/-!
# Equality in the subprobability mixture variance bound

Equality of the weighted moment inequality forces full initial mass, a common supported
mean, and equality of every supported pointwise inequality.
-/

open scoped BigOperators

namespace SSPRK

/-- A sharp mixture bound forces sharp bounds in all positive-weight components. -/
theorem phase_mixture_equality {ι : Type*} [Fintype ι]
    (π x y : ι → ℝ) (k : ℝ) (hk : 0 < k)
    (hπ : ∀ i, 0 ≤ π i) (hmass : ∑ i, π i ≤ 1)
    (hmean : 0 < dotProduct π x)
    (hpoint : ∀ i, (k + 1) * x i ^ 2 ≤ 2 * k * y i)
    (heq : (k + 1) * (dotProduct π x) ^ 2 = 2 * k * dotProduct π y) :
    (∑ i, π i = 1) ∧ ∀ i, 0 < π i →
      x i = dotProduct π x ∧ (k + 1) * x i ^ 2 = 2 * k * y i := by
  have hweighted : (k + 1) * dotProduct π (fun i ↦ x i ^ 2) ≤
      2 * k * dotProduct π y := by
    simp only [dotProduct, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ by
      nlinarith only [mul_le_mul_of_nonneg_left (hpoint i) (hπ i)]
  have hsquare : dotProduct π (fun i ↦ x i ^ 2) ≤ (dotProduct π x) ^ 2 :=
    (mul_le_mul_iff_right₀ (by linarith : 0 < k + 1)).mp (hweighted.trans_eq heq.symm)
  obtain ⟨hmass_eq, hsupport⟩ :=
    weighted_second_moment_equality π x _ hmean hπ hmass rfl hsquare
  have hsquare_eq : dotProduct π (fun i ↦ x i ^ 2) = (dotProduct π x) ^ 2 :=
    le_antisymm hsquare (weighted_mean_sq_le_second_moment π x hπ hmass)
  have hzero : ∑ i, π i * (2 * k * y i - (k + 1) * x i ^ 2) = 0 := by
    have hexpand : ∑ i, π i * (2 * k * y i - (k + 1) * x i ^ 2) =
        2 * k * dotProduct π y - (k + 1) * dotProduct π (fun i ↦ x i ^ 2) := by
      simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hexpand, hsquare_eq, heq, sub_self]
  refine ⟨hmass_eq, fun i hi ↦ ⟨hsupport i hi, ?_⟩⟩
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ ↦ mul_nonneg (hπ j) (sub_nonneg.mpr (hpoint j)))).mp hzero i
      (Finset.mem_univ i)
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left hi.ne')).symm

end SSPRK
