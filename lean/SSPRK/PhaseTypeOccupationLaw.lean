import SSPRK.PhaseTypeRewardLimit
import SSPRK.PhaseTypeEliminationHarmonic
import SSPRK.LaplaceUniqueness

/-!
# Removing actual occupation time

Deleting the first transient state's occupation from a canonical path gives the
Schur-complement phase-type law of Lemma 4.4.
-/

open MeasureTheory

namespace SSPRK.PhaseTypeData

variable {n : ℕ} (d : PhaseTypeData (n + 1))

/-- The elimination reward charges precisely the time spent in the other transient states. -/
theorem recordRewardTotal_eliminationCost (u : ℝ) (records : Records (n + 1)) :
    recordRewardTotal (d.eliminationCost u) records = u * recordOccupationRest records := by
  rw [recordRewardTotal, Fin.sum_univ_succ]
  have htail (i : Fin n) : d.eliminationCost u i.succ.succ = u := by
    have hne : i.succ.succ ≠ (1 : Fin (n + 2)) := by
      change i.succ.succ ≠ (0 : Fin (n + 1)).succ
      exact fun he ↦ Fin.succ_ne_zero i (Fin.succ_inj.mp he)
    simp [eliminationCost, hne]
  rw [show d.eliminationCost u (Fin.succ 0) = 0 by simp [eliminationCost]]
  simp only [htail, zero_mul, zero_add, recordOccupationRest, Finset.mul_sum]

/-- Fixed transient initialization evaluates any observable at that state. -/
theorem integral_initialMeasure_startAt (i : Fin (n + 1)) (f : Fin (n + 2) → ℝ) :
    (∫ x, f x ∂(d.startAt i).initialMeasure) = f i.succ := by
  rw [initialMeasure, PMF.integral_eq_sum, Fin.sum_univ_succ]
  simp [initialPMF_zero, initialPMF_succ, startAt_mass, startAt_initial, apply_ite]

/-- The actual complementary occupation has the deleted-state Laplace transform. -/
theorem integral_exp_neg_occupationRest (u : ℝ) (hu : 0 ≤ u) :
    (∫ records, Real.exp (-u * recordOccupationRest records)
      ∂(d.startAt 0).canonicalRecords) =
        ∫ t, Real.exp (-u * t) ∂d.eliminateZero.measure := by
  have h := (d.startAt 0).integral_exp_neg_recordRewardTotal
    (d.eliminationCost_nonneg u hu) (d.eliminationHarmonic_nonneg u)
    (d.eliminationHarmonic_le_one u hu) (d.eliminationHarmonic_zero u)
    (d.integral_eliminationHarmonic_jumpHoldStepMeasureTotal u hu)
  simpa only [d.recordRewardTotal_eliminationCost, d.integral_initialMeasure_startAt,
    show (0 : Fin (n + 1)).succ = (1 : Fin (n + 2)) by rfl,
    d.eliminationHarmonic_one, neg_mul] using h

/-- Lemma 4.4 identifies the law of the occupation outside the first transient state. -/
theorem canonicalRecords_map_occupationRest :
    (d.startAt 0).canonicalRecords.map recordOccupationRest = d.eliminateZero.measure := by
  letI : IsProbabilityMeasure ((d.startAt 0).canonicalRecords.map recordOccupationRest) :=
    Measure.isProbabilityMeasure_map measurable_recordOccupationRest.aemeasurable
  apply Measure.ext_of_laplace_eq_of_ae_nonneg _ d.eliminateZero.ae_nonneg_measure
  · intro u hu
    rw [integral_map measurable_recordOccupationRest.aemeasurable (by fun_prop)]
    exact d.integral_exp_neg_occupationRest u hu
  · rw [ae_map_iff measurable_recordOccupationRest.aemeasurable (by measurability)]
    exact (d.startAt 0).canonicalRecords_occupationRest_nonneg

end SSPRK.PhaseTypeData
