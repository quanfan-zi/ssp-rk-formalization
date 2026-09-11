import SSPRK.PhaseTypeQMatrix
import SSPRK.CTMC.CanonicalLaw

/-!
# Canonical jump records for phase-type data

The initial phase distribution mixes actual Ionescu-Tulcea record laws. Record zero
is the initial marker; record `n + 1` stores the holding time in state `n` and the
state reached afterwards. These constructions do not assume almost-sure absorption.
-/

open MeasureTheory
open scoped ENNReal

namespace SSPRK.PhaseTypeData

/-- Infinite jump-hold records on the transient states and the absorbing state zero. -/
abbrev Records (s : ℕ) := ℕ → ℝ × Fin (s + 1)

variable {s : ℕ} (d : PhaseTypeData s)

/-- The actual canonical record law, mixed according to the initial phase PMF. -/
noncomputable def canonicalRecords : Measure (Records s) :=
  Measure.sum (fun z ↦ d.initialPMF z • d.qMatrix.canonicalRecordMeasure z)

instance : IsProbabilityMeasure d.canonicalRecords := by
  constructor
  simp only [canonicalRecords, Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact d.initialPMF.tsum_coe

/-- Reading a holding-time coordinate is measurable. -/
theorem measurable_record_holding (n : ℕ) :
    Measurable (fun records : Records s ↦ (records n).1) := by fun_prop

/-- Reading a state coordinate is measurable. -/
theorem measurable_record_state (n : ℕ) :
    Measurable (fun records : Records s ↦ (records n).2) := by fun_prop

/-- A property valid for every initial phase transfers to the mixed record law. -/
theorem ae_canonicalRecords {p : Records s → Prop}
    (hp : ∀ z, ∀ᵐ records ∂d.qMatrix.canonicalRecordMeasure z, p records) :
    ∀ᵐ records ∂d.canonicalRecords, p records :=
  Measure.ae_sum_iff.mpr fun z ↦ Measure.ae_smul_measure (hp z) (d.initialPMF z)

/-- The state in record zero has exactly the initial phase distribution. -/
theorem canonicalRecords_initial_state_law :
    d.canonicalRecords.map (fun records ↦ (records 0).2) = d.initialMeasure := by
  have hmap (z : Fin (s + 1)) :
      (d.qMatrix.canonicalRecordMeasure z).map (fun records ↦ (records 0).2) =
        Measure.dirac z := by
    have heq : (fun records : Records s ↦ (records 0).2) =ᵐ[
        d.qMatrix.canonicalRecordMeasure z] (fun _ ↦ z) :=
      (d.qMatrix.canonicalRecordMeasure_record_zero_eq_init_ae z).mono
        fun records h ↦ congrArg Prod.snd h
    rw [Measure.map_congr heq]
    simp
  rw [canonicalRecords, Measure.map_sum (measurable_record_state 0).aemeasurable]
  simp only [Measure.map_smul, hmap]
  convert Measure.sum_smul_dirac d.initialMeasure using 1
  simp only [initialMeasure, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]

/-- The initial record carries no elapsed time. -/
theorem canonicalRecords_initial_holding_zero :
    ∀ᵐ records ∂d.canonicalRecords, (records 0).1 = 0 := by
  apply d.ae_canonicalRecords
  intro z
  exact (d.qMatrix.canonicalRecordMeasure_record_zero_eq_init_ae z).mono
    fun records h ↦ congrArg Prod.fst h

/-- The full initial record has the initial phase law and deterministic holding marker zero. -/
theorem canonicalRecords_initial_record_law :
    d.canonicalRecords.map (fun records ↦ records 0) =
      d.initialMeasure.map (fun z ↦ ((0 : ℝ), z)) := by
  rw [← d.canonicalRecords_initial_state_law,
    Measure.map_map (by fun_prop) (measurable_record_state 0)]
  apply Measure.map_congr
  filter_upwards [d.canonicalRecords_initial_holding_zero] with records h
  exact Prod.ext h rfl

/-- All sampled holding times after the initial marker are nonnegative. -/
theorem canonicalRecords_holding_nonneg :
    ∀ᵐ records ∂d.canonicalRecords, ∀ n, 0 ≤ (records (n + 1)).1 := by
  apply d.ae_canonicalRecords
  exact d.qMatrix.canonicalRecordMeasure_all_next_holdingTime_nonneg_ae

/-- At state zero the next record is the terminal marker `(0, 0)`. -/
theorem canonicalRecords_zero_next :
    ∀ᵐ records ∂d.canonicalRecords, ∀ n,
      (records n).2 = 0 → records (n + 1) = (0, 0) := by
  apply d.ae_canonicalRecords
  intro z
  filter_upwards
    [d.qMatrix.canonicalRecordMeasure_all_next_state_eq_current_ae_of_absorbing z,
      d.qMatrix.canonicalRecordMeasure_all_next_holdingTime_eq_zero_ae_of_absorbing z]
    with records hstate hhold
  simp only [Ripple.CTMC.QMatrix.currentStateFromHistory_frestrictLe] at hstate hhold
  intro n hn
  have habs : d.qMatrix.IsAbsorbing (records n).2 :=
    hn ▸ d.qMatrix_isAbsorbing_zero
  exact Prod.ext (hhold n habs) ((hstate n habs).trans hn)

/-- Once a record has state zero, every later state is zero and every later hold vanishes. -/
theorem canonicalRecords_zero_persistent :
    ∀ᵐ records ∂d.canonicalRecords, ∀ n m, n ≤ m → (records n).2 = 0 →
      (records m).2 = 0 ∧ (records (m + 1)).1 = 0 := by
  filter_upwards [d.canonicalRecords_zero_next] with records hnext
  intro n m hnm hn
  have hstate : (records m).2 = 0 := by
    induction m, hnm using Nat.le_induction with
    | base => exact hn
    | succ m _ ih => exact congrArg Prod.snd (hnext m ih)
  exact ⟨hstate, congrArg Prod.fst (hnext m hstate)⟩

/-- The first record whose state is absorbing, or infinity when no such record exists. -/
noncomputable def firstAbsorptionIndex (records : Records s) : WithTop ℕ :=
  open Classical in
  if h : ∃ n, (records n).2 = 0 then (Nat.find h : WithTop ℕ) else ⊤

/-- Absorption by step `n` is a finite-coordinate event. -/
theorem firstAbsorptionIndex_le_iff (records : Records s) (n : ℕ) :
    firstAbsorptionIndex records ≤ (n : WithTop ℕ) ↔
      ∃ k ≤ n, (records k).2 = 0 := by
  unfold firstAbsorptionIndex
  split_ifs with h
  · norm_cast
    exact ⟨fun hle ↦ ⟨Nat.find h, hle, Nat.find_spec h⟩,
      fun ⟨k, hk, hzero⟩ ↦ (Nat.find_min' h hzero).trans hk⟩
  · simp only [WithTop.top_le_iff, WithTop.natCast_ne_top, false_iff]
    exact fun ⟨k, _, hk⟩ ↦ h ⟨k, hk⟩

/-- The first absorption index is a measurable extended-natural random variable. -/
theorem measurable_firstAbsorptionIndex :
    Measurable (firstAbsorptionIndex (s := s)) := by
  apply measurable_of_Iic
  intro n
  induction n using WithTop.recTopCoe with
  | top => simp
  | coe n =>
      change MeasurableSet {records : Records s | firstAbsorptionIndex records ≤ (n : WithTop ℕ)}
      simp only [firstAbsorptionIndex_le_iff]
      convert
        MeasurableSet.iUnion fun k : ℕ ↦ MeasurableSet.iUnion fun _ : k ≤ n ↦
          measurableSet_eq_fun (measurable_record_state k)
            (show Measurable (fun _ : Records s ↦ (0 : Fin (s + 1))) from measurable_const)
        using 1
      ext records
      simp

/-- Exact first absorption is a zero state preceded only by nonzero states. -/
theorem firstAbsorptionIndex_eq_iff (records : Records s) (n : ℕ) :
    firstAbsorptionIndex records = (n : WithTop ℕ) ↔
      (records n).2 = 0 ∧ ∀ k < n, (records k).2 ≠ 0 := by
  unfold firstAbsorptionIndex
  split_ifs with h
  · norm_cast
    exact Nat.find_eq_iff h
  · simp only [WithTop.top_ne_natCast, false_iff]
    exact fun ⟨hn, _⟩ ↦ h ⟨n, hn⟩

/-- Infinite absorption index means no record ever reaches the absorbing state. -/
theorem firstAbsorptionIndex_eq_top_iff (records : Records s) :
    firstAbsorptionIndex records = ⊤ ↔ ∀ n, (records n).2 ≠ 0 := by
  unfold firstAbsorptionIndex
  split_ifs with h
  · simp only [WithTop.natCast_ne_top, false_iff, not_forall, not_not]
    exact h
  · simp only [eq_self, true_iff]
    simpa only [not_exists] using h

/-- The nonnegative extended absorption time. A path that never reaches zero has time infinity.
For a finite first-absorption index `n`, exactly the holds in records `1, ..., n` are counted. -/
noncomputable def recordAbsorptionTime (records : Records s) : ℝ≥0∞ :=
  open Classical in
  if firstAbsorptionIndex records = ⊤ then ⊤ else
    ∑' n : ℕ, if (n : WithTop ℕ) < firstAbsorptionIndex records then
      ENNReal.ofReal (records (n + 1)).1 else 0

/-- The extended absorption time is measurable without any properness hypothesis. -/
theorem measurable_recordAbsorptionTime :
    Measurable (recordAbsorptionTime (s := s)) := by
  unfold recordAbsorptionTime
  apply Measurable.ite
    (measurableSet_eq_fun measurable_firstAbsorptionIndex measurable_const) measurable_const
  apply Measurable.tsum
  intro n
  exact Measurable.ite
    (measurableSet_lt measurable_const measurable_firstAbsorptionIndex)
    ((measurable_record_holding (n + 1)).ennreal_ofReal) measurable_const

/-- A finite absorption index gives the correctly indexed finite holding-time sum. -/
theorem recordAbsorptionTime_eq_sum_of_index (records : Records s) (n : ℕ)
    (hn : firstAbsorptionIndex records = (n : WithTop ℕ)) :
    recordAbsorptionTime records =
      ∑ k ∈ Finset.range n, ENNReal.ofReal (records (k + 1)).1 := by
  simp only [recordAbsorptionTime, hn, WithTop.natCast_ne_top, ite_false]
  norm_cast
  rw [tsum_eq_sum (s := Finset.range n) (fun k hk ↦ if_neg (by simpa using hk))]
  exact Finset.sum_congr rfl fun k hk ↦ if_pos (Finset.mem_range.mp hk)

/-- A record trajectory with no absorbing record has infinite absorption time. -/
theorem recordAbsorptionTime_eq_top_of_index (records : Records s)
    (hn : firstAbsorptionIndex records = ⊤) : recordAbsorptionTime records = ⊤ := by
  simp [recordAbsorptionTime, hn]

/-- The absorption time is finite exactly when the path reaches the absorbing state. -/
theorem recordAbsorptionTime_ne_top_iff (records : Records s) :
    recordAbsorptionTime records ≠ ⊤ ↔ firstAbsorptionIndex records ≠ ⊤ := by
  induction h : firstAbsorptionIndex records using WithTop.recTopCoe with
  | top => simp [recordAbsorptionTime_eq_top_of_index records h]
  | coe n =>
      rw [recordAbsorptionTime_eq_sum_of_index records n h]
      simp

end SSPRK.PhaseTypeData
