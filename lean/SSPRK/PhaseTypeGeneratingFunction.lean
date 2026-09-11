import SSPRK.PhaseTypeWeights
import SSPRK.ScaledResolvent

/-!
# Probability generating function of the absorption event count

The Neumann series remains valid at the endpoint one because the original transition
matrix is transient. Pairing it with the initial row and exit vector gives the transform.
-/

namespace SSPRK.PhaseTypeData

variable {s : ℕ} (d : PhaseTypeData s)

/-- The absorption count has a resolvent generating function throughout `[0, 1]`. -/
theorem hasSum_weight_power (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    HasSum (fun n ↦ d.weight n * c ^ (n + 1))
      (c * dotProduct d.initial (((1 - c • d.transition)⁻¹).mulVec d.exit)) := by
  have hdet := d.substochastic.one_sub_smul_det_ne_zero d.transient hc0 hc1
  have hsum := ((d.substochastic.smul hc0 hc1).summable_pow hdet).hasSum
  rw [← (d.substochastic.smul hc0 hc1).inv_eq_tsum hdet] at hsum
  convert (d.hasSum_pairing hsum d.exit).mul_left c using 1
  simp [weight, smul_pow, Matrix.smul_mulVec, dotProduct_smul, pow_succ,
    mul_comm, mul_assoc]

end SSPRK.PhaseTypeData
