import SSPRK.PhaseTypeHoldingLaplace
import SSPRK.PhaseTypeRecordClock

/-!
# Finite-step harmonic expectations on canonical phase-type records

This file propagates a one-step Laplace-harmonic identity through the finite
Ionescu--Tulcea record construction. It proves only finite-step expectation
identities and does not identify an absorption-time law.
-/

open MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators

namespace SSPRK.PhaseTypeData

variable {s : ℕ}

/-- A finite prefix of jump-hold records through index `n`. -/
abbrev RecordHistory (s n : ℕ) :=
  (i : Finset.Iic n) →
    Ripple.CTMC.QMatrix.JumpHoldTrajectorySpace (Fin (s + 1)) i

/-- The elapsed clock encoded by a finite history through record `n`. -/
noncomputable def recordHistoryClock (n : ℕ)
    (hist : (i : Finset.Iic n) → Ripple.CTMC.QMatrix.JumpHoldTrajectorySpace
      (Fin (s + 1)) i) : ℝ :=
  ∑ k : Fin n, (hist ⟨k.val + 1, Finset.mem_Iic.mpr k.isLt⟩).1

/-- The finite-history clock is measurable. -/
theorem measurable_recordHistoryClock (n : ℕ) :
    Measurable (recordHistoryClock (s := s) n) := by
  unfold recordHistoryClock
  fun_prop

/-- Restricting full records to a finite history preserves the finite clock. -/
@[simp]
theorem recordHistoryClock_frestrictLe (n : ℕ) (records : Records s) :
    recordHistoryClock n (Preorder.frestrictLe n records) = recordClock n records := by
  unfold recordHistoryClock recordClock
  simpa only [Preorder.frestrictLe_apply] using
    (Fin.sum_univ_eq_sum_range (fun k ↦ (records (k + 1)).1) n)

/-- The finite-step Laplace-harmonic observable on record trajectories. -/
noncomputable def recordHarmonicIntegrand (u : ℝ) (f : Fin (s + 1) → ℝ)
    (n : ℕ) (records : Records s) : ℝ :=
  Real.exp (-u * recordClock n records) * f (records n).2

/-- Each finite-step Laplace-harmonic observable is measurable. -/
theorem measurable_recordHarmonicIntegrand (u : ℝ) (f : Fin (s + 1) → ℝ)
    (n : ℕ) : Measurable (recordHarmonicIntegrand u f n) := by
  unfold recordHarmonicIntegrand
  exact ((measurable_const.mul (measurable_recordClock n)).exp).mul
    ((Measurable.of_discrete (f := f)).comp (measurable_record_state n))

/-- The integrand lies in `[0, 1]` whenever its clock is nonnegative. -/
theorem recordHarmonicIntegrand_mem_unitInterval {u : ℝ} (hu : 0 ≤ u)
    {f : Fin (s + 1) → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le_one : ∀ x, f x ≤ 1) {n : ℕ} {records : Records s}
    (hclock : 0 ≤ recordClock n records) :
    0 ≤ recordHarmonicIntegrand u f n records ∧
      recordHarmonicIntegrand u f n records ≤ 1 := by
  have hexp_nonneg : 0 ≤ Real.exp (-u * recordClock n records) := (Real.exp_pos _).le
  have hexp_le : Real.exp (-u * recordClock n records) ≤ 1 :=
    Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) hclock)
  constructor
  · exact mul_nonneg hexp_nonneg (hf_nonneg _)
  · exact (mul_le_mul hexp_le (hf_le_one _) (hf_nonneg _) zero_le_one).trans_eq
      (one_mul 1)

/-- The finite-step observable is integrable under a fixed-start canonical record law. -/
theorem integrable_recordHarmonicIntegrand_canonicalRecordMeasure
    (d : PhaseTypeData s) (z : Fin (s + 1)) {u : ℝ} (hu : 0 ≤ u)
    {f : Fin (s + 1) → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le_one : ∀ x, f x ≤ 1) (n : ℕ) :
    Integrable (recordHarmonicIntegrand u f n)
      (d.qMatrix.canonicalRecordMeasure z) := by
  letI := d.qMatrix.isProbabilityMeasure_canonicalRecordMeasure z
  refine (integrable_const (1 : ℝ)).mono'
    (measurable_recordHarmonicIntegrand u f n).aestronglyMeasurable ?_
  filter_upwards
    [d.qMatrix.canonicalRecordMeasure_all_next_holdingTime_nonneg_ae z]
    with records hhold
  have hb := recordHarmonicIntegrand_mem_unitInterval hu hf_nonneg hf_le_one
    (recordClock_nonneg records hhold n)
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

/-- The finite-step observable is integrable under the mixed canonical record law. -/
theorem integrable_recordHarmonicIntegrand
    (d : PhaseTypeData s) {u : ℝ} (hu : 0 ≤ u)
    {f : Fin (s + 1) → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le_one : ∀ x, f x ≤ 1) (n : ℕ) :
    Integrable (recordHarmonicIntegrand u f n) d.canonicalRecords := by
  refine (integrable_const (1 : ℝ)).mono'
    (measurable_recordHarmonicIntegrand u f n).aestronglyMeasurable ?_
  filter_upwards [d.canonicalRecords_clock_nonneg] with records hclock
  have hb := recordHarmonicIntegrand_mem_unitInterval hu hf_nonneg hf_le_one (hclock n)
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

/-- The harmonic observable encoded entirely by a finite history. -/
noncomputable def recordHistoryHarmonicIntegrand (u : ℝ)
    (f : Fin (s + 1) → ℝ) (n : ℕ) (hist : RecordHistory s n) : ℝ :=
  Real.exp (-u * recordHistoryClock n hist) *
    f (Ripple.CTMC.QMatrix.currentStateFromHistory n hist)

/-- The history-level harmonic observable is measurable. -/
theorem measurable_recordHistoryHarmonicIntegrand (u : ℝ)
    (f : Fin (s + 1) → ℝ) (n : ℕ) :
    Measurable (recordHistoryHarmonicIntegrand u f n) := by
  unfold recordHistoryHarmonicIntegrand
  exact ((measurable_const.mul (measurable_recordHistoryClock n)).exp).mul
    ((Measurable.of_discrete (f := f)).comp
      (Ripple.CTMC.QMatrix.measurable_currentStateFromHistory n))

/-- Restriction of the full-record observable to its required history. -/
@[simp]
theorem recordHistoryHarmonicIntegrand_frestrictLe (u : ℝ)
    (f : Fin (s + 1) → ℝ) (n : ℕ) (records : Records s) :
    recordHistoryHarmonicIntegrand u f n (Preorder.frestrictLe n records) =
      recordHarmonicIntegrand u f n records := by
  simp [recordHistoryHarmonicIntegrand, recordHarmonicIntegrand,
    Ripple.CTMC.QMatrix.currentStateFromHistory]

/-- The next-record observable on a finite history paired with its next record. -/
noncomputable def recordHistoryNextHarmonicIntegrand (u : ℝ)
    (f : Fin (s + 1) → ℝ) (n : ℕ)
    (z : RecordHistory s n × (ℝ × Fin (s + 1))) : ℝ :=
  Real.exp (-u * (recordHistoryClock n z.1 + z.2.1)) * f z.2.2

/-- The history-next observable is measurable. -/
theorem measurable_recordHistoryNextHarmonicIntegrand (u : ℝ)
    (f : Fin (s + 1) → ℝ) (n : ℕ) :
    Measurable (recordHistoryNextHarmonicIntegrand u f n) := by
  unfold recordHistoryNextHarmonicIntegrand
  exact (measurable_const.mul
    (((measurable_recordHistoryClock n).comp measurable_fst).add
      (measurable_fst.comp measurable_snd))).exp.mul
    ((Measurable.of_discrete (f := f)).comp (measurable_snd.comp measurable_snd))

/-- Pairing a restricted history with its next record recovers the next-step observable. -/
@[simp]
theorem recordHistoryNextHarmonicIntegrand_frestrictLe (u : ℝ)
    (f : Fin (s + 1) → ℝ) (n : ℕ) (records : Records s) :
    recordHistoryNextHarmonicIntegrand u f n
        (Preorder.frestrictLe n records, records (n + 1)) =
      recordHarmonicIntegrand u f (n + 1) records := by
  rw [recordHistoryNextHarmonicIntegrand, recordHarmonicIntegrand,
    recordHistoryClock_frestrictLe, recordClock_succ]

/-- One-step harmonicity collapses the conditional next-record integral. -/
theorem integral_recordHistoryNextHarmonicIntegrand
    (d : PhaseTypeData s) {u : ℝ} (f : Fin (s + 1) → ℝ)
    (hharmonic : ∀ x,
      (∫ record : ℝ × Fin (s + 1), Real.exp (-u * record.1) * f record.2
        ∂d.qMatrix.jumpHoldStepMeasureTotal x) = f x)
    (n : ℕ) (hist : RecordHistory s n) :
    (∫ record, recordHistoryNextHarmonicIntegrand u f n (hist, record)
      ∂d.qMatrix.jumpHoldTrajectoryStepKernel n hist) =
      recordHistoryHarmonicIntegrand u f n hist := by
  rw [d.qMatrix.jumpHoldTrajectoryStepKernel_apply,
    d.qMatrix.jumpHoldStepKernel_apply]
  simp only [recordHistoryNextHarmonicIntegrand,
    recordHistoryHarmonicIntegrand]
  have hfactor (record : ℝ × Fin (s + 1)) :
      -u * (recordHistoryClock n hist + record.1) =
        -u * recordHistoryClock n hist + -u * record.1 := by
    ring
  simp_rw [hfactor, Real.exp_add, mul_assoc]
  rw [integral_const_mul, hharmonic]

/-- Under a fixed-start canonical law, adjacent finite-step harmonic expectations agree. -/
theorem integral_recordHarmonicIntegrand_succ_canonicalRecordMeasure
    (d : PhaseTypeData s) (z : Fin (s + 1)) {u : ℝ} (hu : 0 ≤ u)
    {f : Fin (s + 1) → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le_one : ∀ x, f x ≤ 1)
    (hharmonic : ∀ x,
      (∫ record : ℝ × Fin (s + 1), Real.exp (-u * record.1) * f record.2
        ∂d.qMatrix.jumpHoldStepMeasureTotal x) = f x)
    (n : ℕ) :
    (∫ records, recordHarmonicIntegrand u f (n + 1) records
      ∂d.qMatrix.canonicalRecordMeasure z) =
      ∫ records, recordHarmonicIntegrand u f n records
        ∂d.qMatrix.canonicalRecordMeasure z := by
  letI : IsMarkovKernel (d.qMatrix.jumpHoldTrajectoryStepKernel n) :=
    d.qMatrix.isMarkovKernel_jumpHoldTrajectoryStepKernel n
  let μ := d.qMatrix.canonicalRecordMeasure z
  let history : Records s → RecordHistory s n := Preorder.frestrictLe n
  let pair : Records s → RecordHistory s n × (ℝ × Fin (s + 1)) :=
    fun records ↦ (history records, records (n + 1))
  let g := recordHistoryNextHarmonicIntegrand u f n
  have hhistory_meas : Measurable history := by
    exact Preorder.measurable_frestrictLe n
  have hpair_meas : Measurable pair := by
    dsimp only [pair]
    fun_prop
  have hg_meas : Measurable g := measurable_recordHistoryNextHarmonicIntegrand u f n
  have hsucc : Integrable (recordHarmonicIntegrand u f (n + 1)) μ := by
    exact d.integrable_recordHarmonicIntegrand_canonicalRecordMeasure z hu
      hf_nonneg hf_le_one (n + 1)
  have hg_map : Integrable g (μ.map pair) := by
    apply (integrable_map_measure hg_meas.aestronglyMeasurable
      hpair_meas.aemeasurable).2
    have hfun : g ∘ pair = recordHarmonicIntegrand u f (n + 1) := by
      funext records
      exact recordHistoryNextHarmonicIntegrand_frestrictLe u f n records
    rw [hfun]
    exact hsucc
  have hjoint :
      μ.map pair = μ.map history ⊗ₘ d.qMatrix.jumpHoldTrajectoryStepKernel n := by
    simpa only [μ, pair, history] using
      d.qMatrix.canonicalRecordMeasure_history_next z n
  have hg_joint :
      Integrable g (μ.map history ⊗ₘ d.qMatrix.jumpHoldTrajectoryStepKernel n) := by
    rw [← hjoint]
    exact hg_map
  calc
    (∫ records, recordHarmonicIntegrand u f (n + 1) records ∂μ) =
        ∫ p, g p ∂μ.map pair := by
      rw [integral_map hpair_meas.aemeasurable hg_map.aestronglyMeasurable]
      simp only [g, pair, history,
        recordHistoryNextHarmonicIntegrand_frestrictLe]
    _ = ∫ p, g p
          ∂(μ.map history ⊗ₘ d.qMatrix.jumpHoldTrajectoryStepKernel n) := by
      rw [← hjoint]
    _ = ∫ hist, ∫ record, g (hist, record)
          ∂d.qMatrix.jumpHoldTrajectoryStepKernel n hist ∂μ.map history :=
      ProbabilityTheory.integral_compProd hg_joint
    _ = ∫ hist, recordHistoryHarmonicIntegrand u f n hist ∂μ.map history := by
      apply integral_congr_ae
      filter_upwards with hist
      exact d.integral_recordHistoryNextHarmonicIntegrand f hharmonic n hist
    _ = ∫ records, recordHarmonicIntegrand u f n records ∂μ := by
      rw [integral_map hhistory_meas.aemeasurable
        (measurable_recordHistoryHarmonicIntegrand u f n).aestronglyMeasurable]
      simp only [history,
        recordHistoryHarmonicIntegrand_frestrictLe]

/-- A fixed-start finite-step harmonic expectation equals its initial value. -/
theorem integral_recordHarmonicIntegrand_canonicalRecordMeasure_eq
    (d : PhaseTypeData s) (z : Fin (s + 1)) {u : ℝ} (hu : 0 ≤ u)
    {f : Fin (s + 1) → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le_one : ∀ x, f x ≤ 1)
    (hharmonic : ∀ x,
      (∫ record : ℝ × Fin (s + 1), Real.exp (-u * record.1) * f record.2
        ∂d.qMatrix.jumpHoldStepMeasureTotal x) = f x)
    (n : ℕ) :
    (∫ records, recordHarmonicIntegrand u f n records
      ∂d.qMatrix.canonicalRecordMeasure z) = f z := by
  induction n with
  | zero =>
      letI := d.qMatrix.isProbabilityMeasure_canonicalRecordMeasure z
      simp only [recordHarmonicIntegrand, recordClock_zero, mul_zero,
        Real.exp_zero, one_mul]
      calc
        (∫ records, f (records 0).2 ∂d.qMatrix.canonicalRecordMeasure z) =
            ∫ _records, f z ∂d.qMatrix.canonicalRecordMeasure z := by
          apply integral_congr_ae
          filter_upwards
            [d.qMatrix.canonicalRecordMeasure_record_zero_eq_init_ae z]
            with records hrecord
          rw [hrecord]
        _ = f z := by simp
  | succ n ih =>
      rw [d.integral_recordHarmonicIntegrand_succ_canonicalRecordMeasure z hu
        hf_nonneg hf_le_one hharmonic n]
      exact ih

/-- A bounded finite-state observable is integrable under the initial phase law. -/
theorem integrable_stateFun_initialMeasure
    (d : PhaseTypeData s) {f : Fin (s + 1) → ℝ}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_le_one : ∀ x, f x ≤ 1) :
    Integrable f d.initialMeasure := by
  refine (integrable_const (1 : ℝ)).mono'
    (Measurable.of_discrete (f := f)).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg x)]
  exact hf_le_one x

/-- Every mixed finite-step harmonic expectation equals the initial-law expectation. -/
theorem integral_recordHarmonicIntegrand_eq_initial
    (d : PhaseTypeData s) {u : ℝ} (hu : 0 ≤ u)
    {f : Fin (s + 1) → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le_one : ∀ x, f x ≤ 1)
    (hharmonic : ∀ x,
      (∫ record : ℝ × Fin (s + 1), Real.exp (-u * record.1) * f record.2
        ∂d.qMatrix.jumpHoldStepMeasureTotal x) = f x)
    (n : ℕ) :
    (∫ records, recordHarmonicIntegrand u f n records ∂d.canonicalRecords) =
      ∫ x, f x ∂d.initialMeasure := by
  have hint := d.integrable_recordHarmonicIntegrand hu hf_nonneg hf_le_one n
  rw [canonicalRecords] at hint ⊢
  rw [integral_sum_measure hint]
  simp_rw [integral_smul_measure,
    d.integral_recordHarmonicIntegrand_canonicalRecordMeasure_eq _ hu
      hf_nonneg hf_le_one hharmonic n]
  change (∑' z, (d.initialPMF z).toReal * f z) = ∫ x, f x ∂d.initialPMF.toMeasure
  rw [PMF.integral_eq_tsum d.initialPMF f
    (d.integrable_stateFun_initialMeasure hf_nonneg hf_le_one)]
  simp only [smul_eq_mul]

end SSPRK.PhaseTypeData
