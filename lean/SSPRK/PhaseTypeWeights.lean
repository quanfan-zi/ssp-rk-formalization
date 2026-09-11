import SSPRK.PhaseTypeData

/-!
# Absorption weights of a finite phase-type representation

The absorption weights have the prescribed initial mass. Their counting moments are
obtained from the convergent Neumann series of the transient transition matrix.
-/

open scoped BigOperators

namespace SSPRK.PhaseTypeData

variable {s : ℕ} (d : PhaseTypeData s)

theorem exit_nonneg (i : Fin s) : 0 ≤ d.exit i := by
  simpa [exit, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec, dotProduct,
    Matrix.one_apply] using
    sub_nonneg.mpr (d.substochastic.row_sum_le i)

theorem weight_nonneg (n : ℕ) : 0 ≤ d.weight n := by
  unfold weight Matrix.mulVec dotProduct
  exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (d.initial_nonneg i)
    (Finset.sum_nonneg fun j _ ↦
      mul_nonneg ((d.substochastic.pow n).nonneg i j) (d.exit_nonneg j))

theorem hasSum_pairing {f : ℕ → Matrix (Fin s) (Fin s) ℝ}
    {a : Matrix (Fin s) (Fin s) ℝ} (h : HasSum f a) (v : Fin s → ℝ) :
    HasSum (fun n ↦ dotProduct d.initial ((f n).mulVec v))
      (dotProduct d.initial (a.mulVec v)) := by
  unfold Matrix.mulVec dotProduct
  exact hasSum_sum fun i _ ↦ (hasSum_sum fun j _ ↦
    ((Pi.hasSum.mp (Pi.hasSum.mp h i) j).mul_right (v j))).mul_left (d.initial i)

theorem green_mulVec_exit : d.green.mulVec d.exit = fun _ ↦ 1 := by
  rw [green, exit, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr d.transient), Matrix.one_mulVec]

theorem hasSum_weight : HasSum d.weight d.mass := by
  have h : HasSum (fun n : ℕ ↦ d.transition ^ n) d.green := by
    rw [green, d.substochastic.inv_eq_tsum d.transient]
    exact (d.substochastic.summable_pow d.transient).hasSum
  simpa [weight, d.green_mulVec_exit, mass, dotProduct] using d.hasSum_pairing h d.exit

theorem summable_weight : Summable d.weight := d.hasSum_weight.summable

theorem tsum_weight : ∑' n, d.weight n = d.mass := d.hasSum_weight.tsum_eq

end SSPRK.PhaseTypeData
