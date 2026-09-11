import SSPRK.PhaseTypeAbsorptionLimit
import SSPRK.PhaseTypeLaplaceHarmonic
import SSPRK.PhaseTypeLaplaceGenerator
import SSPRK.PhaseTypeAbsorptionProper
import SSPRK.LaplaceUniqueness
import SSPRK.PhaseTypeGeneratorMoments
import SSPRK.PhaseTypeRecordHarmonic

/-!
# The phase-type law as a canonical absorption-time distribution

The finite-state harmonic Laplace function identifies the distribution of the actual
absorption time read from canonical jump records.
-/

open MeasureTheory Filter
open scoped Topology

namespace SSPRK.PhaseTypeData

variable {s : ℕ} (d : PhaseTypeData s)

/-- The elapsed time to absorption is finite almost surely. -/
theorem canonicalRecords_absorptionTime_ne_top_ae :
    ∀ᵐ records ∂d.canonicalRecords, recordAbsorptionTime records ≠ ⊤ :=
  d.canonicalRecords_firstAbsorptionIndex_ne_top_ae.mono fun records hfinite ↦
    (recordAbsorptionTime_ne_top_iff records).2 hfinite

/-- Averaging the harmonic function over the initial distribution gives the PH transform. -/
theorem integral_initialMeasure_laplaceHarmonic (u : ℝ) (hu : 0 ≤ u) :
    (∫ x, d.laplaceHarmonic u x ∂d.initialMeasure) =
      ∫ t, Real.exp (-u * t) ∂d.measure := by
  rw [initialMeasure, PMF.integral_eq_sum, Fin.sum_univ_succ]
  simp only [initialPMF_zero, initialPMF_succ, laplaceHarmonic_zero,
    smul_eq_mul, mul_one, d.laplaceHarmonic_succ_eq_resolvent u hu,
    ENNReal.toReal_ofReal (d.initial_nonneg _)]
  rw [ENNReal.toReal_ofReal (show 0 ≤ 1 - d.mass from sub_nonneg.mpr d.initial_mass_le),
    d.integral_exp_neg_mul_eq_generator u hu]
  rfl

/-- The absorption time of the actual canonical jump-record process has the PH law. -/
theorem canonicalRecords_map_absorptionTime :
    d.canonicalRecords.map (fun records ↦ (recordAbsorptionTime records).toReal) =
      d.measure := by
  have hm : Measurable (fun records : Records s ↦ (recordAbsorptionTime records).toReal) :=
    measurable_recordAbsorptionTime.ennreal_toReal
  letI : IsProbabilityMeasure
      (d.canonicalRecords.map (fun records ↦ (recordAbsorptionTime records).toReal)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  apply Measure.ext_of_laplace_eq_of_ae_nonneg _ d.ae_nonneg_measure
  · intro u hu
    rw [integral_map hm.aemeasurable (by fun_prop)]
    have ht := d.tendsto_integral_record_laplace_observable
      d.canonicalRecords_firstAbsorptionIndex_ne_top_ae hu (d.laplaceHarmonic u)
      (fun x ↦ ⟨d.laplaceHarmonic_nonneg u x, d.laplaceHarmonic_le_one u hu x⟩)
      (d.laplaceHarmonic_zero u)
    have hconst : ∀ n, (∫ records,
        Real.exp (-u * recordClock n records) * d.laplaceHarmonic u (records n).2
          ∂d.canonicalRecords) = ∫ x, d.laplaceHarmonic u x ∂d.initialMeasure := by
      exact d.integral_recordHarmonicIntegrand_eq_initial hu
        (d.laplaceHarmonic_nonneg u) (d.laplaceHarmonic_le_one u hu)
        (d.integral_laplaceHarmonic_jumpHoldStepMeasureTotal u hu)
    simp only [hconst] at ht
    exact (tendsto_nhds_unique ht tendsto_const_nhds).trans
      (d.integral_initialMeasure_laplaceHarmonic u hu)
  · rw [ae_map_iff hm.aemeasurable (by measurability)]
    exact ae_of_all _ fun records ↦ ENNReal.toReal_nonneg

/-- Every natural power of the actual absorption time is integrable. -/
theorem integrable_recordAbsorptionTime_pow (k : ℕ) :
    Integrable (fun records ↦ (recordAbsorptionTime records).toReal ^ k)
      d.canonicalRecords := by
  have h := d.integrable_pow_measure k
  rw [← d.canonicalRecords_map_absorptionTime] at h
  exact (integrable_map_measure (continuous_pow k).aestronglyMeasurable
    measurable_recordAbsorptionTime.ennreal_toReal.aemeasurable).mp h

/-- Actual canonical absorption times satisfy the generator-inverse moment formula. -/
theorem integral_recordAbsorptionTime_pow (k : ℕ) (hk : 0 < k) :
    (∫ records, (recordAbsorptionTime records).toReal ^ k ∂d.canonicalRecords) =
      (k.factorial : ℝ) *
        dotProduct d.initial ((((-d.generator)⁻¹) ^ k).mulVec (fun _ ↦ 1)) := by
  rw [← d.integral_pow_eq_generator k hk, ← d.canonicalRecords_map_absorptionTime,
    integral_map measurable_recordAbsorptionTime.ennreal_toReal.aemeasurable (by fun_prop)]

end SSPRK.PhaseTypeData
