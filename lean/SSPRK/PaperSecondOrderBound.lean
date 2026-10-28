import SSPRK.PaperRKPH

/-! # The normalized PH variance estimate in the second-order optimality proof -/

open MeasureTheory

namespace SSPRK.AbsolutelyMonotoneAt

variable {s : ℕ} {A : Matrix (Fin s) (Fin s) ℝ} {b : Fin s → ℝ} {r : ℝ}

/-- The paper's minimum-variance estimate for the conditional positive-time PH law. -/
theorem normalized_second_order_variance (h : AbsolutelyMonotoneAt A b r) (hr : 0 < r)
    (hs : 0 < s) (hord1 : dotProduct b (fun _ ↦ (1 : ℝ)) = 1)
    (hord2 : dotProduct b (A.mulVec (fun _ ↦ (1 : ℝ))) = 1 / 2) :
    1 + 1 / (s : ℝ) ≤ rkSigma r b A * (1 + 2 / r) := by
  have hm := h.phaseType_mass_pos hr hord1
  rw [h.phaseType_mass hr] at hm
  have hm1 : ∫ x, x ∂(h.normalizedPhaseType hr hord1).measure = r / rkSigma r b A := by
    simpa only [normalizedPhaseType, pow_one, h.phaseType_integral_id hr hord1,
      h.phaseType_mass hr] using
      (h.phaseType hr).normalizeInitial_integral_pow (h.phaseType_mass_pos hr hord1) 1
        (by omega)
  have hm2 : ∫ x, x ^ 2 ∂(h.normalizedPhaseType hr hord1).measure =
      (r ^ 2 + 2 * r) / rkSigma r b A := by
    simpa only [normalizedPhaseType, h.phaseType_integral_sq hr hord1 hord2,
      h.phaseType_mass hr] using
      (h.phaseType hr).normalizeInitial_integral_pow (h.phaseType_mass_pos hr hord1) 2
        (by omega)
  have hbound := (h.normalizedPhaseType hr hord1).variance_lower_bound hs
  rw [(h.normalizedPhaseType hr hord1).variance_measure, hm1, hm2] at hbound
  have hsreal : 0 < (s : ℝ) := Nat.cast_pos.mpr hs
  have hbound' := (div_le_iff₀ hsreal).mp hbound
  have hscaled := mul_le_mul_of_nonneg_left hbound' (sq_nonneg (rkSigma r b A))
  field_simp [hm.ne'] at hscaled
  have htarget := (div_le_iff₀ hsreal).mpr (show
      (s : ℝ) + 1 ≤ rkSigma r b A * (1 + 2 / r) * (s : ℝ) by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hr)).mp
    field_simp [hr.ne']
    nlinarith)
  simpa only [add_div, div_self hsreal.ne', one_div] using htarget

/-- The normalized variance estimate and the transient mass bound imply `r ≤ 2s`. -/
theorem second_order_bound_normalized (h : AbsolutelyMonotoneAt A b r) (hr : 0 < r)
    (hs : 0 < s) (hord1 : dotProduct b (fun _ ↦ (1 : ℝ)) = 1)
    (hord2 : dotProduct b (A.mulVec (fun _ ↦ (1 : ℝ))) = 1 / 2) :
    r ≤ 2 * (s : ℝ) := by
  have hvariance := h.normalized_second_order_variance hr hs hord1 hord2
  have hmass := rkSigma_le_one r b A h.output_mass
  have hbound := hvariance.trans (mul_le_of_le_one_left (by positivity) hmass)
  have hrecip : 1 / (s : ℝ) ≤ 2 / r := by linarith
  have hcross := (div_le_div_iff₀ (Nat.cast_pos.mpr hs) hr).mp hrecip
  simpa only [one_mul] using hcross

end SSPRK.AbsolutelyMonotoneAt
