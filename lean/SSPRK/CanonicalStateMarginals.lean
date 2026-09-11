import Ripple.CTMC.CanonicalLaw

/-!
# State marginals of canonical jump records

The states in the canonical jump-hold record process have exactly the iterated laws of
the embedded discrete Markov chain, including absorbing states.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.CTMC.QMatrix

variable {s : ℕ} (Q : QMatrix (Fin (s + 1)))

/-- Discarding the holding time from a total jump record gives the embedded transition. -/
theorem jumpHoldStepMeasureTotal_map_snd (x : Fin (s + 1)) :
    (Q.jumpHoldStepMeasureTotal x).map Prod.snd = Q.embeddedStepMeasure x := by
  by_cases hx : Q.IsAbsorbing x
  · rw [Q.jumpHoldStepMeasureTotal_of_absorbing hx, Measure.map_dirac' (by fun_prop)]
    simp [embeddedStepMeasure, embeddedDTMC, show Q.exitRate x = 0 from hx,
      PMF.toMeasure_pure]
  · rw [Q.jumpHoldStepMeasureTotal_of_nonabsorbing hx, Q.jumpHoldStepMeasure_map_snd hx]

/-- The state marginal of the total jump kernel, including absorbing states. -/
noncomputable def embeddedStateKernel : Kernel (Fin (s + 1)) (Fin (s + 1)) :=
  Q.jumpHoldStepKernel.map Prod.snd

@[simp]
theorem embeddedStateKernel_apply (x : Fin (s + 1)) :
    Q.embeddedStateKernel x = Q.embeddedStepMeasure x := by
  rw [embeddedStateKernel, Kernel.map_apply _ measurable_snd]
  exact Q.jumpHoldStepMeasureTotal_map_snd x

instance : IsMarkovKernel Q.embeddedStateKernel := by
  constructor
  intro x
  rw [embeddedStateKernel_apply]
  exact Q.isProbabilityMeasure_embeddedStepMeasure x

/-- The law of the state at record index `n`. -/
noncomputable def canonicalStateLaw (x : Fin (s + 1)) (n : ℕ) : Measure (Fin (s + 1)) :=
  (Q.canonicalRecordMeasure x).map (fun records ↦ (records n).2)

/-- At each record, the state law advances by the embedded transition kernel. -/
theorem canonicalStateLaw_succ (x : Fin (s + 1)) (n : ℕ) :
    Q.canonicalStateLaw x (n + 1) = Q.embeddedStateKernel ∘ₘ Q.canonicalStateLaw x n := by
  have h := Q.canonicalRecordMeasure_history_next x n
  letI := Q.isMarkovKernel_jumpHoldTrajectoryStepKernel n
  have hm := congrArg (fun μ ↦ μ.snd.map Prod.snd) h
  simp only [Measure.snd_compProd] at hm
  rw [Measure.map_comp _ _ measurable_snd] at hm
  simp only [Measure.snd] at hm
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at hm
  change Q.canonicalStateLaw x (n + 1) = _ at hm
  rw [hm]
  ext a ha
  rw [Measure.bind_apply ha (Kernel.aemeasurable _),
    Measure.bind_apply ha (Kernel.aemeasurable _)]
  rw [lintegral_map (((Q.jumpHoldTrajectoryStepKernel n).map Prod.snd).measurable_coe ha)
    (Preorder.measurable_frestrictLe n), canonicalStateLaw,
    lintegral_map (Q.embeddedStateKernel.measurable_coe ha) (by fun_prop)]
  apply lintegral_congr
  intro records
  rw [Kernel.map_apply _ measurable_snd, jumpHoldTrajectoryStepKernel_apply,
    jumpHoldStepKernel_apply, jumpHoldStepMeasureTotal_map_snd, embeddedStateKernel_apply]
  rfl

/-- The initial state in the canonical record process has its prescribed Dirac law. -/
theorem canonicalStateLaw_zero (x : Fin (s + 1)) :
    Q.canonicalStateLaw x 0 = Measure.dirac x := by
  have h := Q.canonicalRecordMeasure_record_zero_eq_init_ae x
  have hm : (fun records ↦ (records 0).2) =ᵐ[Q.canonicalRecordMeasure x] fun _ ↦ x :=
    h.mono fun records hr ↦ congrArg Prod.snd hr
  rw [canonicalStateLaw, Measure.map_congr hm]
  simp

/-- The state marginal at each record index is the embedded chain's iterated PMF. -/
theorem canonicalStateLaw_eq_stepN (x : Fin (s + 1)) (n : ℕ) :
    Q.canonicalStateLaw x n = (Q.embeddedDTMC.stepN n x).toMeasure := by
  induction n with
  | zero => simp [canonicalStateLaw_zero, PMF.toMeasure_pure]
  | succ n ih =>
      rw [canonicalStateLaw_succ, ih]
      ext a ha
      rw [Measure.bind_apply ha (Kernel.aemeasurable _), DTMC.stepN,
        PMF.toMeasure_bind_apply _ _ a ha, lintegral_fintype]
      simp [embeddedStateKernel_apply, embeddedStepMeasure, tsum_fintype, mul_comm]

end Ripple.CTMC.QMatrix
