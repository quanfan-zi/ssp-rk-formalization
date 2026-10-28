import SSPRK.RKPhaseType
import SSPRK.PhaseTypeNormalization

/-!
# The normalized RK--PH representation in V2.10

The paper uses the initial row `rkOmega / rkSigma`. The existing output law permits
an atom at zero; this module removes that atom by normalizing its positive initial mass.
-/

namespace SSPRK.AbsolutelyMonotoneAt

variable {s : ℕ} {A : Matrix (Fin s) (Fin s) ℝ} {b : Fin s → ℝ} {r : ℝ}

/-- Consistency forces the transformed initial row to have strictly positive mass. -/
theorem phaseType_mass_pos (h : AbsolutelyMonotoneAt A b r) (hr : 0 < r)
    (hord1 : dotProduct b (fun _ ↦ (1 : ℝ)) = 1) : 0 < (h.phaseType hr).mass := by
  rw [h.phaseType_mass hr]
  exact rkSigma_pos r b A hr (rkOmega_nonneg r b A hr.le h.output_nonneg)
    (rkOmega_N_ones_eq r b A h.det_ne_zero hord1)

/-- The normalized positive-time representation used in Proposition 3.1. -/
noncomputable def normalizedPhaseType (h : AbsolutelyMonotoneAt A b r) (hr : 0 < r)
    (hord1 : dotProduct b (fun _ ↦ (1 : ℝ)) = 1) : PhaseTypeData s :=
  (h.phaseType hr).normalizeInitial (h.phaseType_mass_pos hr hord1)

@[simp]
theorem normalizedPhaseType_mass (h : AbsolutelyMonotoneAt A b r) (hr : 0 < r)
    (hord1 : dotProduct b (fun _ ↦ (1 : ℝ)) = 1) :
    (h.normalizedPhaseType hr hord1).mass = 1 :=
  (h.phaseType hr).normalizeInitial_mass (h.phaseType_mass_pos hr hord1)

@[simp]
theorem normalizedPhaseType_generator (h : AbsolutelyMonotoneAt A b r) (hr : 0 < r)
    (hord1 : dotProduct b (fun _ ↦ (1 : ℝ)) = 1) :
    (h.normalizedPhaseType hr hord1).generator = -rkM r A :=
  h.phaseType_generator hr

@[simp]
theorem normalizedPhaseType_green (h : AbsolutelyMonotoneAt A b r) (hr : 0 < r)
    (hord1 : dotProduct b (fun _ ↦ (1 : ℝ)) = 1) :
    (h.normalizedPhaseType hr hord1).green = rkN r A :=
  h.phaseType_green hr

@[simp]
theorem normalizedPhaseType_initial (h : AbsolutelyMonotoneAt A b r) (hr : 0 < r)
    (hord1 : dotProduct b (fun _ ↦ (1 : ℝ)) = 1) :
    (h.normalizedPhaseType hr hord1).initial = (rkSigma r b A)⁻¹ • rkOmega r b A := by
  change (h.phaseType hr).mass⁻¹ • rkOmega r b A = _
  rw [h.phaseType_mass hr]

@[simp]
theorem normalizedPhaseType_rate (h : AbsolutelyMonotoneAt A b r) (hr : 0 < r)
    (hord1 : dotProduct b (fun _ ↦ (1 : ℝ)) = 1) :
    (h.normalizedPhaseType hr hord1).rate = 1 := rfl

end SSPRK.AbsolutelyMonotoneAt
