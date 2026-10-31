import SSPRK.PhaseTypeMoments
import SSPRK.GreenReachability

open MeasureTheory

namespace SSPRK.PhaseTypeData

/-- A PH law whose initial transient mass is one has strictly positive mean. -/
theorem integral_id_pos_of_mass_one {s : ℕ} (d : PhaseTypeData s)
    (hmass : d.mass = 1) : 0 < ∫ x, x ∂d.measure := by
  rw [d.integral_id_measure]
  apply div_pos _ d.rate_pos
  have hrow (i : Fin s) : 1 ≤ d.green.mulVec (fun _ ↦ 1) i :=
    d.substochastic.one_le_inv_mulVec_one d.transient i
  have hle : d.mass ≤ dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)) := by
    unfold mass dotProduct
    apply Finset.sum_le_sum
    intro i _
    simpa using mul_le_mul_of_nonneg_left (hrow i) (d.initial_nonneg i)
  linarith

end SSPRK.PhaseTypeData
