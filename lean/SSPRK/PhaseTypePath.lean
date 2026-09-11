import SSPRK.PhaseTypeRecordClock
import SSPRK.PhaseTypeAbsorptionProper

/-!
# The continuous-time path read from canonical phase records

The state is read from the first holding interval whose right endpoint lies after
the requested time. When no such endpoint exists it is the absorbing state zero.
This gives the correct state after absorption even though record clocks then plateau.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace SSPRK.PhaseTypeData

variable {s : ℕ}

/-- The actual continuous-time state read from jump records, with absorbing fallback zero. -/
noncomputable def recordStateAt (t : ℝ) (records : Records s) : Fin (s + 1) :=
  open Classical in
  if h : ∃ n, t < recordClock (n + 1) records then (records (Nat.find h)).2 else 0

/-- The readout is zero if all record clocks have already passed. -/
theorem recordStateAt_eq_zero_of_no_future (t : ℝ) (records : Records s)
    (h : ∀ n, recordClock (n + 1) records ≤ t) : recordStateAt t records = 0 := by
  simp [recordStateAt, not_exists.mpr (fun n ↦ not_lt.mpr (h n))]

/-- The first interval whose right endpoint lies after time `t` determines the readout. -/
theorem recordStateAt_eq_of_first (t : ℝ) (records : Records s) (n : ℕ)
    (hn : t < recordClock (n + 1) records)
    (hmin : ∀ k < n, ¬t < recordClock (k + 1) records) :
    recordStateAt t records = (records n).2 := by
  have hex : ∃ k, t < recordClock (k + 1) records := ⟨n, hn⟩
  have hfind : Nat.find hex = n := (Nat.find_eq_iff hex).2 ⟨hn, hmin⟩
  simp [recordStateAt, hex, hfind]

/-- Nonnegative holding times make the record clocks monotone. -/
theorem recordClock_monotone (records : Records s)
    (hhold : ∀ n, 0 ≤ (records (n + 1)).1) : Monotone (fun n ↦ recordClock n records) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [recordClock_succ]
  exact le_add_of_nonneg_right (hhold n)

/-- On a nonempty holding interval the readout is the corresponding recorded state. -/
theorem recordStateAt_eq_of_sojourn (records : Records s)
    (hhold : ∀ n, 0 ≤ (records (n + 1)).1) (n : ℕ) (t : ℝ)
    (ht : t ∈ Ico (recordClock n records) (recordClock (n + 1) records)) :
    recordStateAt t records = (records n).2 := by
  apply recordStateAt_eq_of_first t records n ht.2
  intro k hk
  exact not_lt.mpr (((recordClock_monotone records hhold) (Nat.succ_le_of_lt hk)).trans ht.1)

/-- The readout event is a countable union of finite-history events and the terminal event. -/
theorem recordStateAt_eq_iff (t : ℝ) (records : Records s) (a : Fin (s + 1)) :
    recordStateAt t records = a ↔
      ((∀ n, ¬t < recordClock (n + 1) records) ∧ 0 = a) ∨
        ∃ n, (t < recordClock (n + 1) records ∧
          ∀ k < n, ¬t < recordClock (k + 1) records) ∧ (records n).2 = a := by
  by_cases h : ∃ n, t < recordClock (n + 1) records
  · constructor
    · intro ha
      exact Or.inr ⟨Nat.find h, ⟨Nat.find_spec h, fun k hk ↦ Nat.find_min h hk⟩,
        by simpa [recordStateAt, h] using ha⟩
    · rintro (⟨hno, _⟩ | ⟨n, ⟨hn, hmin⟩, ha⟩)
      · exact (hno (Nat.find h) (Nat.find_spec h)).elim
      · exact (recordStateAt_eq_of_first t records n hn hmin).trans ha
  · simp only [recordStateAt, dif_neg h]
    have hno : ∀ n, ¬t < recordClock (n + 1) records := not_exists.mp h
    exact ⟨fun ha ↦ Or.inl ⟨hno, ha⟩,
      fun ha ↦ ha.elim And.right (fun ⟨n, ⟨hn, _⟩, _⟩ ↦ (hno n hn).elim)⟩

/-- The state readout is jointly measurable in physical time and the record trajectory. -/
theorem measurable_recordStateAt :
    Measurable (fun p : ℝ × Records s ↦ recordStateAt p.1 p.2) := by
  apply measurable_to_countable'
  intro a
  change MeasurableSet {p : ℝ × Records s | recordStateAt p.1 p.2 = a}
  simp only [recordStateAt_eq_iff, Set.setOf_or, Set.setOf_and, Set.setOf_exists,
    Set.setOf_forall]
  have hlt (n : ℕ) : MeasurableSet {p : ℝ × Records s |
      p.1 < recordClock (n + 1) p.2} :=
    measurableSet_lt measurable_fst ((measurable_recordClock (n + 1)).comp measurable_snd)
  have hstate (n : ℕ) : MeasurableSet {p : ℝ × Records s | (p.2 n).2 = a} :=
    measurableSet_eq_fun ((measurable_record_state n).comp measurable_snd) measurable_const
  exact ((MeasurableSet.iInter fun n ↦ (hlt n).compl).inter (by measurability)).union
    (MeasurableSet.iUnion fun n ↦
      ((hlt n).inter (MeasurableSet.iInter fun k ↦
        MeasurableSet.iInter fun _ : k < n ↦ (hlt k).compl)).inter (hstate n))

/-- For a fixed record trajectory the state is a measurable function of time. -/
theorem measurable_recordStateAt_time (records : Records s) :
    Measurable (fun t ↦ recordStateAt t records) :=
  measurable_recordStateAt.comp (measurable_id.prodMk measurable_const)

/-- At a fixed time the state is a measurable random variable on the record space. -/
theorem measurable_recordStateAt_records (t : ℝ) :
    Measurable (recordStateAt (s := s) t) :=
  measurable_recordStateAt.comp (measurable_const.prodMk measurable_id)

/-- Every nonzero phase state is nonabsorbing for the actual Q-matrix. -/
theorem qMatrix_not_absorbing_of_ne_zero (d : PhaseTypeData s) (z : Fin (s + 1))
    (hz : z ≠ 0) : ¬d.qMatrix.IsAbsorbing z := by
  induction z using Fin.cases with
  | zero => exact (hz rfl).elim
  | succ i => exact d.qMatrix_not_isAbsorbing_succ i

/-- Before absorption, each hold is positive and the next jump changes the state. -/
theorem canonicalRecords_transient_step (d : PhaseTypeData s) :
    ∀ᵐ records ∂d.canonicalRecords, ∀ n, (records n).2 ≠ 0 →
      0 < (records (n + 1)).1 ∧ (records (n + 1)).2 ≠ (records n).2 := by
  apply d.ae_canonicalRecords
  intro z
  filter_upwards
    [d.qMatrix.canonicalRecordMeasure_all_next_holdingTime_pos_ae_of_nonabsorbing z,
      d.qMatrix.canonicalRecordMeasure_all_next_state_ne_current_ae_of_nonabsorbing z]
    with records hpos hne
  simp only [Ripple.CTMC.QMatrix.currentStateFromHistory_frestrictLe] at hpos hne
  intro n hn
  have hnonabs := d.qMatrix_not_absorbing_of_ne_zero (records n).2 hn
  exact ⟨hpos n hnonabs, hne n hnonabs⟩

/-- Almost every canonical path agrees with its state record on every holding interval. -/
theorem canonicalRecords_stateAt_sojourn (d : PhaseTypeData s) :
    ∀ᵐ records ∂d.canonicalRecords, ∀ n t,
      t ∈ Ico (recordClock n records) (recordClock (n + 1) records) →
        recordStateAt t records = (records n).2 :=
  d.canonicalRecords_holding_nonneg.mono fun records hhold ↦
    recordStateAt_eq_of_sojourn records hhold

/-- The continuous-time path starts at its initial recorded state, including initial absorption. -/
theorem canonicalRecords_stateAt_zero (d : PhaseTypeData s) :
    ∀ᵐ records ∂d.canonicalRecords, recordStateAt 0 records = (records 0).2 := by
  filter_upwards [d.canonicalRecords_transient_step, d.canonicalRecords_zero_persistent]
    with records hstep hpersist
  by_cases hz : (records 0).2 = 0
  · rw [hz]
    apply recordStateAt_eq_zero_of_no_future
    intro n
    have hclock := recordClock_eq_of_holding_zero records 0 (n + 1) (Nat.zero_le _)
      (fun m hm ↦ (hpersist 0 m hm hz).2)
    simpa only [recordClock_zero] using hclock.le
  · apply recordStateAt_eq_of_first 0 records 0
    · simpa only [recordClock_succ, recordClock_zero, zero_add] using (hstep 0 hz).1
    · simp

/-- The continuous-time process has the specified initial phase distribution. -/
theorem canonicalRecords_initial_path_law (d : PhaseTypeData s) :
    d.canonicalRecords.map (recordStateAt 0) = d.initialMeasure := by
  rw [Measure.map_congr d.canonicalRecords_stateAt_zero, d.canonicalRecords_initial_state_law]

/-- Every step strictly before the first absorbing record has a positive hold and a true jump. -/
theorem canonicalRecords_step_before_absorption (d : PhaseTypeData s) :
    ∀ᵐ records ∂d.canonicalRecords, ∀ n : ℕ,
      (n : WithTop ℕ) < firstAbsorptionIndex records →
        0 < (records (n + 1)).1 ∧ (records (n + 1)).2 ≠ (records n).2 := by
  filter_upwards [d.canonicalRecords_transient_step] with records hstep
  intro n hn
  apply hstep n
  intro hz
  exact (not_le_of_gt hn) ((firstAbsorptionIndex_le_iff records n).2 ⟨n, le_rfl, hz⟩)

/-- A monotone clock that has plateaued at `k` has zero state from that clock value onward. -/
theorem recordStateAt_eq_zero_after_clock (records : Records s) (k : ℕ)
    (hhold : ∀ n, 0 ≤ (records (n + 1)).1)
    (hconstant : ∀ n, k ≤ n → recordClock n records = recordClock k records)
    (t : ℝ) (ht : recordClock k records ≤ t) : recordStateAt t records = 0 := by
  apply recordStateAt_eq_zero_of_no_future
  intro n
  by_cases hn : n + 1 ≤ k
  · exact ((recordClock_monotone records hhold) hn).trans ht
  · rw [hconstant (n + 1) (le_of_not_ge hn)]
    exact ht

/-- Before a finite first absorption clock, the readout cannot be the absorbing state. -/
theorem recordStateAt_ne_zero_before_index (records : Records s) (k : ℕ)
    (hk : firstAbsorptionIndex records = (k : WithTop ℕ)) (t : ℝ)
    (ht0 : 0 ≤ t) (ht : t < recordClock k records) : recordStateAt t records ≠ 0 := by
  cases k with
  | zero => simp only [recordClock_zero] at ht; exact (not_lt_of_ge ht0 ht).elim
  | succ k =>
      have hex : ∃ n, t < recordClock (n + 1) records := ⟨k, ht⟩
      have hfind : Nat.find hex < k + 1 := Nat.lt_succ_of_le (Nat.find_min' hex ht)
      have hne := ((firstAbsorptionIndex_eq_iff records (k + 1)).mp hk).2
        (Nat.find hex) hfind
      simpa only [recordStateAt, dif_pos hex] using hne

/-- At nonnegative times the actual path is absorbed exactly from its absorption time onward. -/
theorem canonicalRecords_stateAt_eq_zero_iff (d : PhaseTypeData s) :
    ∀ᵐ records ∂d.canonicalRecords, ∀ t, 0 ≤ t →
      (recordStateAt t records = 0 ↔ (recordAbsorptionTime records).toReal ≤ t) := by
  filter_upwards [d.canonicalRecords_holding_nonneg,
    d.canonicalRecords_clock_constant_after_absorption,
    d.canonicalRecords_firstAbsorptionIndex_ne_top_ae] with records hhold hconstant hfinite
  induction hindex : firstAbsorptionIndex records using WithTop.recTopCoe with
  | top => exact (hfinite hindex).elim
  | coe k =>
      intro t ht0
      rw [recordAbsorptionTime_toReal_eq_clock records k hindex hhold]
      constructor
      · intro hz
        by_contra ht
        exact recordStateAt_ne_zero_before_index records k hindex t ht0 (lt_of_not_ge ht) hz
      · intro ht
        exact recordStateAt_eq_zero_after_clock records k hhold (hconstant k hindex) t ht

/-- The path remains at zero after its actual absorption time. -/
theorem canonicalRecords_stateAt_after_absorption (d : PhaseTypeData s) :
    ∀ᵐ records ∂d.canonicalRecords, ∀ t,
      (recordAbsorptionTime records).toReal ≤ t → recordStateAt t records = 0 := by
  filter_upwards [d.canonicalRecords_stateAt_eq_zero_iff] with records hiff
  intro t ht
  exact (hiff t (ENNReal.toReal_nonneg.trans ht)).2 ht

/-- The path is nonabsorbing throughout the half-open interval before absorption. -/
theorem canonicalRecords_stateAt_before_absorption (d : PhaseTypeData s) :
    ∀ᵐ records ∂d.canonicalRecords, ∀ t,
      t ∈ Ico 0 (recordAbsorptionTime records).toReal → recordStateAt t records ≠ 0 := by
  filter_upwards [d.canonicalRecords_stateAt_eq_zero_iff] with records hiff
  intro t ht hz
  exact (not_le_of_gt ht.2) ((hiff t ht.1).1 hz)

/-- The record absorption time is the first nonnegative physical time at state zero. -/
theorem canonicalRecords_absorptionTime_isLeast (d : PhaseTypeData s) :
    ∀ᵐ records ∂d.canonicalRecords,
      IsLeast {t : ℝ | 0 ≤ t ∧ recordStateAt t records = 0}
        (recordAbsorptionTime records).toReal := by
  filter_upwards [d.canonicalRecords_stateAt_eq_zero_iff] with records hiff
  refine ⟨⟨ENNReal.toReal_nonneg, (hiff _ ENNReal.toReal_nonneg).2 le_rfl⟩, ?_⟩
  intro t ht
  exact (hiff t ht.1).1 ht.2

end SSPRK.PhaseTypeData
