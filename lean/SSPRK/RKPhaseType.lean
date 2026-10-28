import SSPRK.PhaseTypeVariance
import SSPRK.SSPRadius
import SSPRK.RKSubstochastic

/-!
# Phase-type probability laws from feasible Runge--Kutta tableaux

The output row of the absolute-monotonicity transform supplies the initial mass.
Its missing mass is an atom at zero, and the uniformizing clock has rate one.
-/

open MeasureTheory

namespace SSPRK

namespace AbsolutelyMonotoneAt

variable {s : ℕ} {A : Matrix (Fin s) (Fin s) ℝ} {b : Fin s → ℝ} {r : ℝ}

/-- The probability representation attached to a positive feasible RK parameter. -/
noncomputable def phaseType (h : AbsolutelyMonotoneAt A b r) (hr : 0 < r) :
    PhaseTypeData s where
  transition := rkP r A
  initial := rkOmega r b A
  rate := 1
  rate_pos := zero_lt_one
  substochastic := rkP_substochastic r A h.det_ne_zero h.stages h.matrix_nonneg
  transient := one_sub_rkP_det_ne_zero r A h.det_ne_zero
  initial_nonneg := rkOmega_nonneg r b A hr.le h.output_nonneg
  initial_mass_le := by
    simpa [rkSigma, dotProduct, ones] using rkSigma_le_one r b A h.output_mass

variable (h : AbsolutelyMonotoneAt A b r) (hr : 0 < r)

/-- The transient generator is minus the inverse shifted RK matrix. -/
theorem phaseType_generator : (h.phaseType hr).generator = -rkM r A := by
  simp only [PhaseTypeData.generator, phaseType, one_smul, rkP]
  abel

/-- The Green matrix of this probability law is the shifted RK matrix. -/
theorem phaseType_green : (h.phaseType hr).green = rkN r A := by
  exact (rkN_eq_inv_one_sub_rkP r A h.det_ne_zero).symm

/-- The initial transient mass agrees with the transformed output mass. -/
theorem phaseType_mass : (h.phaseType hr).mass = rkSigma r b A := by
  simp [PhaseTypeData.mass, phaseType, rkSigma, dotProduct, ones]

/-- The first RK order condition gives the actual mean of the PH law. -/
theorem phaseType_integral_id
    (hord1 : dotProduct b (fun _ ↦ (1 : ℝ)) = 1) :
    ∫ x, x ∂(h.phaseType hr).measure = r := by
  rw [(h.phaseType hr).integral_id_measure, h.phaseType_green hr]
  simpa only [phaseType, div_one, Matrix.dotProduct_mulVec, ones] using
    rkOmega_N_ones_eq r b A h.det_ne_zero hord1

/-- The first two RK order conditions give the actual second PH moment. -/
theorem phaseType_integral_sq
    (hord1 : dotProduct b (fun _ ↦ (1 : ℝ)) = 1)
    (hord2 : dotProduct b (A.mulVec (fun _ ↦ (1 : ℝ))) = 1 / 2) :
    ∫ x, x ^ 2 ∂(h.phaseType hr).measure = r ^ 2 + 2 * r := by
  rw [(h.phaseType hr).integral_sq_measure, h.phaseType_green hr]
  change 2 * dotProduct (rkOmega r b A)
    ((rkN r A).mulVec ((rkN r A).mulVec (ones s))) / (1 : ℝ) ^ 2 = _
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    rkOmega_N_sq_ones_eq r b A h.det_ne_zero hord1 hord2]
  ring

/-- The variance of the transformed output law is exactly twice the feasible parameter. -/
theorem phaseType_variance
    (hord1 : dotProduct b (fun _ ↦ (1 : ℝ)) = 1)
    (hord2 : dotProduct b (A.mulVec (fun _ ↦ (1 : ℝ))) = 1 / 2) :
    ProbabilityTheory.variance (fun x : ℝ ↦ x) (h.phaseType hr).measure = 2 * r := by
  rw [(h.phaseType hr).variance_measure, h.phaseType_integral_id hr hord1,
    h.phaseType_integral_sq hr hord1 hord2]
  ring

include h hr in
/-- The second-order SSP bound follows directly from the probability-law variance bound. -/
theorem second_order_bound_via_phaseType (hs : 0 < s)
    (hord1 : dotProduct b (fun _ ↦ (1 : ℝ)) = 1)
    (hord2 : dotProduct b (A.mulVec (fun _ ↦ (1 : ℝ))) = 1 / 2) :
    r ≤ 2 * (s : ℝ) := by
  have hbound := (h.phaseType hr).variance_lower_bound hs
  rw [h.phaseType_integral_id hr hord1, h.phaseType_variance hr hord1 hord2] at hbound
  have hbound' := (div_le_iff₀ (Nat.cast_pos.mpr hs)).mp hbound
  nlinarith

end AbsolutelyMonotoneAt
end SSPRK
