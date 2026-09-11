import SSPRK.PhaseTypeRecordHarmonic

/-!
# Finite-step reward-harmonic expectations on canonical phase-type records

The reward clock weights each holding interval by a nonnegative function of the
state occupied during that interval. This file propagates a one-step
reward-harmonic identity through finite canonical record histories.
-/

open MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators

namespace SSPRK.PhaseTypeData

variable {s : ℕ}

/-- Accumulated state-dependent reward through record `n`. -/
noncomputable def recordRewardClock (c : Fin (s + 1) → ℝ) (n : ℕ)
    (records : Records s) : ℝ :=
  ∑ k ∈ Finset.range n, c (records k).2 * (records (k + 1)).1

/-- Each finite reward clock is measurable. -/
theorem measurable_recordRewardClock (c : Fin (s + 1) → ℝ) (n : ℕ) :
    Measurable (recordRewardClock c n) := by
  unfold recordRewardClock
  apply Finset.measurable_sum
  intro k _
  exact ((Measurable.of_discrete (f := c)).comp (measurable_record_state k)).mul
    (measurable_record_holding (k + 1))

@[simp]
theorem recordRewardClock_zero (c : Fin (s + 1) → ℝ) (records : Records s) :
    recordRewardClock c 0 records = 0 := by
  simp [recordRewardClock]

/-- The next reward-clock value adds the cost of the current holding interval. -/
theorem recordRewardClock_succ (c : Fin (s + 1) → ℝ) (n : ℕ)
    (records : Records s) :
    recordRewardClock c (n + 1) records =
      recordRewardClock c n records + c (records n).2 * (records (n + 1)).1 := by
  exact Finset.sum_range_succ _ n

/-- Nonnegative costs and holding times give nonnegative reward clocks. -/
theorem recordRewardClock_nonneg {c : Fin (s + 1) → ℝ}
    (hc : ∀ x, 0 ≤ c x) (records : Records s)
    (hhold : ∀ n, 0 ≤ (records (n + 1)).1) (n : ℕ) :
    0 ≤ recordRewardClock c n records :=
  Finset.sum_nonneg fun k _ ↦ mul_nonneg (hc _) (hhold k)

/-- Canonical reward clocks are almost surely nonnegative. -/
theorem canonicalRecords_rewardClock_nonneg (d : PhaseTypeData s)
    {c : Fin (s + 1) → ℝ} (hc : ∀ x, 0 ≤ c x) :
    ∀ᵐ records ∂d.canonicalRecords, ∀ n, 0 ≤ recordRewardClock c n records :=
  d.canonicalRecords_holding_nonneg.mono fun records hhold n ↦
    recordRewardClock_nonneg hc records hhold n

/-- The finite-step reward-harmonic observable on record trajectories. -/
noncomputable def recordRewardHarmonicIntegrand (c f : Fin (s + 1) → ℝ)
    (n : ℕ) (records : Records s) : ℝ :=
  Real.exp (-recordRewardClock c n records) * f (records n).2

/-- Each finite-step reward-harmonic observable is measurable. -/
theorem measurable_recordRewardHarmonicIntegrand (c f : Fin (s + 1) → ℝ)
    (n : ℕ) : Measurable (recordRewardHarmonicIntegrand c f n) := by
  unfold recordRewardHarmonicIntegrand
  exact (measurable_recordRewardClock c n).neg.exp.mul
    ((Measurable.of_discrete (f := f)).comp (measurable_record_state n))

/-- The reward integrand lies in `[0, 1]` when its clock is nonnegative. -/
theorem recordRewardHarmonicIntegrand_mem_unitInterval
    {c f : Fin (s + 1) → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le_one : ∀ x, f x ≤ 1) {n : ℕ} {records : Records s}
    (hclock : 0 ≤ recordRewardClock c n records) :
    0 ≤ recordRewardHarmonicIntegrand c f n records ∧
      recordRewardHarmonicIntegrand c f n records ≤ 1 := by
  have hexp_nonneg : 0 ≤ Real.exp (-recordRewardClock c n records) :=
    (Real.exp_pos _).le
  have hexp_le : Real.exp (-recordRewardClock c n records) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hclock)
  constructor
  · exact mul_nonneg hexp_nonneg (hf_nonneg _)
  · exact (mul_le_mul hexp_le (hf_le_one _) (hf_nonneg _) zero_le_one).trans_eq
      (one_mul 1)

/-- The reward observable is integrable under a fixed-start canonical record law. -/
theorem integrable_recordRewardHarmonicIntegrand_canonicalRecordMeasure
    (d : PhaseTypeData s) (z : Fin (s + 1)) {c : Fin (s + 1) → ℝ}
    (hc : ∀ x, 0 ≤ c x) {f : Fin (s + 1) → ℝ}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_le_one : ∀ x, f x ≤ 1) (n : ℕ) :
    Integrable (recordRewardHarmonicIntegrand c f n)
      (d.qMatrix.canonicalRecordMeasure z) := by
  letI := d.qMatrix.isProbabilityMeasure_canonicalRecordMeasure z
  refine (integrable_const (1 : ℝ)).mono'
    (measurable_recordRewardHarmonicIntegrand c f n).aestronglyMeasurable ?_
  filter_upwards
    [d.qMatrix.canonicalRecordMeasure_all_next_holdingTime_nonneg_ae z]
    with records hhold
  have hb := recordRewardHarmonicIntegrand_mem_unitInterval hf_nonneg hf_le_one
    (recordRewardClock_nonneg hc records hhold n)
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

/-- The reward observable is integrable under the mixed canonical record law. -/
theorem integrable_recordRewardHarmonicIntegrand
    (d : PhaseTypeData s) {c : Fin (s + 1) → ℝ} (hc : ∀ x, 0 ≤ c x)
    {f : Fin (s + 1) → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le_one : ∀ x, f x ≤ 1) (n : ℕ) :
    Integrable (recordRewardHarmonicIntegrand c f n) d.canonicalRecords := by
  refine (integrable_const (1 : ℝ)).mono'
    (measurable_recordRewardHarmonicIntegrand c f n).aestronglyMeasurable ?_
  filter_upwards [d.canonicalRecords_rewardClock_nonneg hc] with records hclock
  have hb := recordRewardHarmonicIntegrand_mem_unitInterval hf_nonneg hf_le_one (hclock n)
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

/-- The reward clock encoded by a finite history through record `n`. -/
noncomputable def recordRewardHistoryClock (c : Fin (s + 1) → ℝ) (n : ℕ)
    (hist : RecordHistory s n) : ℝ :=
  ∑ k : Fin n,
    c (hist ⟨k.val, Finset.mem_Iic.mpr (Nat.le_of_lt k.isLt)⟩).2 *
      (hist ⟨k.val + 1, Finset.mem_Iic.mpr k.isLt⟩).1

/-- The finite-history reward clock is measurable. -/
theorem measurable_recordRewardHistoryClock (c : Fin (s + 1) → ℝ) (n : ℕ) :
    Measurable (recordRewardHistoryClock c n) := by
  unfold recordRewardHistoryClock
  fun_prop

/-- Restricting full records to a finite history preserves the reward clock. -/
@[simp]
theorem recordRewardHistoryClock_frestrictLe (c : Fin (s + 1) → ℝ)
    (n : ℕ) (records : Records s) :
    recordRewardHistoryClock c n (Preorder.frestrictLe n records) =
      recordRewardClock c n records := by
  unfold recordRewardHistoryClock recordRewardClock
  simpa only [Preorder.frestrictLe_apply] using
    (Fin.sum_univ_eq_sum_range
      (fun k ↦ c (records k).2 * (records (k + 1)).1) n)

/-- The reward-harmonic observable encoded by a finite history. -/
noncomputable def recordRewardHistoryHarmonicIntegrand
    (c f : Fin (s + 1) → ℝ) (n : ℕ) (hist : RecordHistory s n) : ℝ :=
  Real.exp (-recordRewardHistoryClock c n hist) *
    f (Ripple.CTMC.QMatrix.currentStateFromHistory n hist)

/-- The finite-history reward-harmonic observable is measurable. -/
theorem measurable_recordRewardHistoryHarmonicIntegrand
    (c f : Fin (s + 1) → ℝ) (n : ℕ) :
    Measurable (recordRewardHistoryHarmonicIntegrand c f n) := by
  unfold recordRewardHistoryHarmonicIntegrand
  exact (measurable_recordRewardHistoryClock c n).neg.exp.mul
    ((Measurable.of_discrete (f := f)).comp
      (Ripple.CTMC.QMatrix.measurable_currentStateFromHistory n))

/-- Restriction of the full reward observable to its required history. -/
@[simp]
theorem recordRewardHistoryHarmonicIntegrand_frestrictLe
    (c f : Fin (s + 1) → ℝ) (n : ℕ) (records : Records s) :
    recordRewardHistoryHarmonicIntegrand c f n (Preorder.frestrictLe n records) =
      recordRewardHarmonicIntegrand c f n records := by
  simp [recordRewardHistoryHarmonicIntegrand, recordRewardHarmonicIntegrand,
    Ripple.CTMC.QMatrix.currentStateFromHistory]

/-- The next-record reward observable on a finite history and its next record. -/
noncomputable def recordRewardHistoryNextHarmonicIntegrand
    (c f : Fin (s + 1) → ℝ) (n : ℕ)
    (z : RecordHistory s n × (ℝ × Fin (s + 1))) : ℝ :=
  Real.exp (-(recordRewardHistoryClock c n z.1 +
    c (Ripple.CTMC.QMatrix.currentStateFromHistory n z.1) * z.2.1)) * f z.2.2

/-- The history-next reward observable is measurable. -/
theorem measurable_recordRewardHistoryNextHarmonicIntegrand
    (c f : Fin (s + 1) → ℝ) (n : ℕ) :
    Measurable (recordRewardHistoryNextHarmonicIntegrand c f n) := by
  unfold recordRewardHistoryNextHarmonicIntegrand
  have hclock : Measurable
      (fun z : RecordHistory s n × (ℝ × Fin (s + 1)) ↦
        recordRewardHistoryClock c n z.1) :=
    (measurable_recordRewardHistoryClock c n).comp measurable_fst
  have hstate : Measurable
      (fun z : RecordHistory s n × (ℝ × Fin (s + 1)) ↦
        Ripple.CTMC.QMatrix.currentStateFromHistory n z.1) :=
    (Ripple.CTMC.QMatrix.measurable_currentStateFromHistory n).comp measurable_fst
  have hcost : Measurable
      (fun z : RecordHistory s n × (ℝ × Fin (s + 1)) ↦
        c (Ripple.CTMC.QMatrix.currentStateFromHistory n z.1)) :=
    (Measurable.of_discrete (f := c)).comp hstate
  have hhold : Measurable
      (fun z : RecordHistory s n × (ℝ × Fin (s + 1)) ↦ z.2.1) :=
    measurable_fst.comp measurable_snd
  exact (hclock.add (hcost.mul hhold)).neg.exp.mul
    ((Measurable.of_discrete (f := f)).comp (measurable_snd.comp measurable_snd))

/-- Pairing a restricted history with its next record recovers the next reward observable. -/
@[simp]
theorem recordRewardHistoryNextHarmonicIntegrand_frestrictLe
    (c f : Fin (s + 1) → ℝ) (n : ℕ) (records : Records s) :
    recordRewardHistoryNextHarmonicIntegrand c f n
        (Preorder.frestrictLe n records, records (n + 1)) =
      recordRewardHarmonicIntegrand c f (n + 1) records := by
  rw [recordRewardHistoryNextHarmonicIntegrand, recordRewardHarmonicIntegrand,
    recordRewardHistoryClock_frestrictLe, recordRewardClock_succ]
  rfl

/-- One-step reward harmonicity collapses the conditional next-record integral. -/
theorem integral_recordRewardHistoryNextHarmonicIntegrand
    (d : PhaseTypeData s) (c f : Fin (s + 1) → ℝ)
    (hharmonic : ∀ x,
      (∫ record : ℝ × Fin (s + 1),
        Real.exp (-(c x) * record.1) * f record.2
        ∂d.qMatrix.jumpHoldStepMeasureTotal x) = f x)
    (n : ℕ) (hist : RecordHistory s n) :
    (∫ record, recordRewardHistoryNextHarmonicIntegrand c f n (hist, record)
      ∂d.qMatrix.jumpHoldTrajectoryStepKernel n hist) =
      recordRewardHistoryHarmonicIntegrand c f n hist := by
  rw [d.qMatrix.jumpHoldTrajectoryStepKernel_apply,
    d.qMatrix.jumpHoldStepKernel_apply]
  simp only [recordRewardHistoryNextHarmonicIntegrand,
    recordRewardHistoryHarmonicIntegrand]
  have hfactor (record : ℝ × Fin (s + 1)) :
      -(recordRewardHistoryClock c n hist +
          c (Ripple.CTMC.QMatrix.currentStateFromHistory n hist) * record.1) =
        -recordRewardHistoryClock c n hist +
          -(c (Ripple.CTMC.QMatrix.currentStateFromHistory n hist)) * record.1 := by
    ring
  simp_rw [hfactor, Real.exp_add, mul_assoc]
  rw [integral_const_mul, hharmonic]

/-- Under a fixed-start canonical law, adjacent reward-harmonic expectations agree. -/
theorem integral_recordRewardHarmonicIntegrand_succ_canonicalRecordMeasure
    (d : PhaseTypeData s) (z : Fin (s + 1)) {c : Fin (s + 1) → ℝ}
    (hc : ∀ x, 0 ≤ c x) {f : Fin (s + 1) → ℝ}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_le_one : ∀ x, f x ≤ 1)
    (hharmonic : ∀ x,
      (∫ record : ℝ × Fin (s + 1),
        Real.exp (-(c x) * record.1) * f record.2
        ∂d.qMatrix.jumpHoldStepMeasureTotal x) = f x)
    (n : ℕ) :
    (∫ records, recordRewardHarmonicIntegrand c f (n + 1) records
      ∂d.qMatrix.canonicalRecordMeasure z) =
      ∫ records, recordRewardHarmonicIntegrand c f n records
        ∂d.qMatrix.canonicalRecordMeasure z := by
  letI : IsMarkovKernel (d.qMatrix.jumpHoldTrajectoryStepKernel n) :=
    d.qMatrix.isMarkovKernel_jumpHoldTrajectoryStepKernel n
  let μ := d.qMatrix.canonicalRecordMeasure z
  let history : Records s → RecordHistory s n := Preorder.frestrictLe n
  let pair : Records s → RecordHistory s n × (ℝ × Fin (s + 1)) :=
    fun records ↦ (history records, records (n + 1))
  let g := recordRewardHistoryNextHarmonicIntegrand c f n
  have hhistory_meas : Measurable history := Preorder.measurable_frestrictLe n
  have hpair_meas : Measurable pair := by
    dsimp only [pair]
    fun_prop
  have hg_meas : Measurable g :=
    measurable_recordRewardHistoryNextHarmonicIntegrand c f n
  have hsucc : Integrable (recordRewardHarmonicIntegrand c f (n + 1)) μ := by
    exact d.integrable_recordRewardHarmonicIntegrand_canonicalRecordMeasure z hc
      hf_nonneg hf_le_one (n + 1)
  have hg_map : Integrable g (μ.map pair) := by
    apply (integrable_map_measure hg_meas.aestronglyMeasurable
      hpair_meas.aemeasurable).2
    have hfun : g ∘ pair = recordRewardHarmonicIntegrand c f (n + 1) := by
      funext records
      exact recordRewardHistoryNextHarmonicIntegrand_frestrictLe c f n records
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
    (∫ records, recordRewardHarmonicIntegrand c f (n + 1) records ∂μ) =
        ∫ p, g p ∂μ.map pair := by
      rw [integral_map hpair_meas.aemeasurable hg_map.aestronglyMeasurable]
      simp only [g, pair, history,
        recordRewardHistoryNextHarmonicIntegrand_frestrictLe]
    _ = ∫ p, g p
          ∂(μ.map history ⊗ₘ d.qMatrix.jumpHoldTrajectoryStepKernel n) := by
      rw [← hjoint]
    _ = ∫ hist, ∫ record, g (hist, record)
          ∂d.qMatrix.jumpHoldTrajectoryStepKernel n hist ∂μ.map history :=
      ProbabilityTheory.integral_compProd hg_joint
    _ = ∫ hist, recordRewardHistoryHarmonicIntegrand c f n hist
          ∂μ.map history := by
      apply integral_congr_ae
      filter_upwards with hist
      exact d.integral_recordRewardHistoryNextHarmonicIntegrand c f
        hharmonic n hist
    _ = ∫ records, recordRewardHarmonicIntegrand c f n records ∂μ := by
      rw [integral_map hhistory_meas.aemeasurable
        (measurable_recordRewardHistoryHarmonicIntegrand c f n).aestronglyMeasurable]
      simp only [history,
        recordRewardHistoryHarmonicIntegrand_frestrictLe]

/-- A fixed-start finite-step reward-harmonic expectation equals its initial value. -/
theorem integral_recordRewardHarmonicIntegrand_canonicalRecordMeasure_eq
    (d : PhaseTypeData s) (z : Fin (s + 1)) {c : Fin (s + 1) → ℝ}
    (hc : ∀ x, 0 ≤ c x) {f : Fin (s + 1) → ℝ}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_le_one : ∀ x, f x ≤ 1)
    (hharmonic : ∀ x,
      (∫ record : ℝ × Fin (s + 1),
        Real.exp (-(c x) * record.1) * f record.2
        ∂d.qMatrix.jumpHoldStepMeasureTotal x) = f x)
    (n : ℕ) :
    (∫ records, recordRewardHarmonicIntegrand c f n records
      ∂d.qMatrix.canonicalRecordMeasure z) = f z := by
  induction n with
  | zero =>
      letI := d.qMatrix.isProbabilityMeasure_canonicalRecordMeasure z
      simp only [recordRewardHarmonicIntegrand, recordRewardClock_zero,
        neg_zero, Real.exp_zero, one_mul]
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
      rw [d.integral_recordRewardHarmonicIntegrand_succ_canonicalRecordMeasure
        z hc hf_nonneg hf_le_one hharmonic n]
      exact ih

/-- Every mixed finite-step reward-harmonic expectation equals the initial expectation. -/
theorem integral_recordRewardHarmonicIntegrand_eq_initial
    (d : PhaseTypeData s) {c : Fin (s + 1) → ℝ} (hc : ∀ x, 0 ≤ c x)
    {f : Fin (s + 1) → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le_one : ∀ x, f x ≤ 1)
    (hharmonic : ∀ x,
      (∫ record : ℝ × Fin (s + 1),
        Real.exp (-(c x) * record.1) * f record.2
        ∂d.qMatrix.jumpHoldStepMeasureTotal x) = f x)
    (n : ℕ) :
    (∫ records, recordRewardHarmonicIntegrand c f n records
      ∂d.canonicalRecords) = ∫ x, f x ∂d.initialMeasure := by
  have hint := d.integrable_recordRewardHarmonicIntegrand hc hf_nonneg hf_le_one n
  rw [canonicalRecords] at hint ⊢
  rw [integral_sum_measure hint]
  simp_rw [integral_smul_measure,
    d.integral_recordRewardHarmonicIntegrand_canonicalRecordMeasure_eq _ hc
      hf_nonneg hf_le_one hharmonic n]
  change (∑' z, (d.initialPMF z).toReal * f z) = ∫ x, f x ∂d.initialPMF.toMeasure
  rw [PMF.integral_eq_tsum d.initialPMF f
    (d.integrable_stateFun_initialMeasure hf_nonneg hf_le_one)]
  simp only [smul_eq_mul]

end SSPRK.PhaseTypeData
