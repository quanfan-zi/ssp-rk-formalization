import SSPRK.PhaseTypeRecordClock
import SSPRK.PhaseTypeAbsorptionProper

/-!
# Occupation times on the actual canonical jump records

Occupation in transient state `i` counts record `k + 1`'s holding time when record `k`
has state `i.succ`, up to the first absorbing record. Infinite-index records receive the
value zero; canonical properness makes this convention irrelevant almost surely.
-/

open MeasureTheory
open scoped BigOperators

namespace SSPRK.PhaseTypeData

variable {s : ℕ}

/-- A natural-valued absorption count, with default zero for records that never absorb. -/
noncomputable def recordAbsorptionCount (records : Records s) : ℕ :=
  (firstAbsorptionIndex records).untopD 0

/-- The finite occupation accumulated through the first `n` holding intervals. -/
noncomputable def recordOccupationUntil (i : Fin s) (n : ℕ) (records : Records s) : ℝ :=
  ∑ k ∈ Finset.range n, if (records k).2 = i.succ then (records (k + 1)).1 else 0

/-- Total occupation of one transient state before the first absorbing record. -/
noncomputable def recordOccupation (i : Fin s) (records : Records s) : ℝ :=
  recordOccupationUntil i (recordAbsorptionCount records) records

/-- The defaulted finite absorption count is measurable. -/
theorem measurable_recordAbsorptionCount :
    Measurable (recordAbsorptionCount (s := s)) := by
  exact (measurable_of_countable (fun k : WithTop ℕ ↦ k.untopD 0)).comp
    measurable_firstAbsorptionIndex

/-- Finite occupation uses only finitely many measurable record coordinates. -/
theorem measurable_recordOccupationUntil (i : Fin s) (n : ℕ) :
    Measurable (recordOccupationUntil i n) := by
  unfold recordOccupationUntil
  apply Finset.measurable_sum
  intro k _
  exact Measurable.ite
    (measurableSet_eq_fun (measurable_record_state k) measurable_const)
    (measurable_record_holding (k + 1)) measurable_const

/-- Occupation stopped at the random absorption count is measurable. -/
theorem measurable_recordOccupation (i : Fin s) : Measurable (recordOccupation i) := by
  have hf : Measurable (fun p : ℕ × Records s ↦ recordOccupationUntil i p.1 p.2) :=
    measurable_from_prod_countable_right (measurable_recordOccupationUntil i)
  exact hf.comp (measurable_recordAbsorptionCount.prodMk measurable_id)

/-- A finite first-absorption index is unchanged by the natural-valued default convention. -/
theorem recordAbsorptionCount_eq_of_index (records : Records s) (n : ℕ)
    (hn : firstAbsorptionIndex records = (n : WithTop ℕ)) :
    recordAbsorptionCount records = n := by
  rw [recordAbsorptionCount, hn]
  rfl

/-- On nonabsorbing records the default occupation value is zero. -/
theorem recordOccupation_eq_zero_of_index_top (records : Records s) (i : Fin s)
    (hn : firstAbsorptionIndex records = ⊤) : recordOccupation i records = 0 := by
  simp [recordOccupation, recordAbsorptionCount, hn, recordOccupationUntil]

/-- At a finite absorption index the occupation is its correctly indexed finite sum. -/
theorem recordOccupation_eq_sum_of_index (records : Records s) (i : Fin s) (n : ℕ)
    (hn : firstAbsorptionIndex records = (n : WithTop ℕ)) :
    recordOccupation i records =
      ∑ k ∈ Finset.range n, if (records k).2 = i.succ then (records (k + 1)).1 else 0 := by
  rw [recordOccupation, recordAbsorptionCount_eq_of_index records n hn]
  rfl

/-- Nonnegative holds give nonnegative occupation for each transient state. -/
theorem recordOccupation_nonneg (records : Records s)
    (hhold : ∀ n, 0 ≤ (records (n + 1)).1) (i : Fin s) :
    0 ≤ recordOccupation i records := by
  unfold recordOccupation recordOccupationUntil
  exact Finset.sum_nonneg fun k _ ↦ by split_ifs <;> first | exact hhold k | exact le_rfl

/-- Canonical occupation times are simultaneously nonnegative almost surely. -/
theorem canonicalRecords_occupation_nonneg (d : PhaseTypeData s) :
    ∀ᵐ records ∂d.canonicalRecords, ∀ i, 0 ≤ recordOccupation i records :=
  d.canonicalRecords_holding_nonneg.mono fun records hhold ↦ recordOccupation_nonneg records hhold

/-- Before the first absorbing record, summing transient occupations gives the finite clock. -/
theorem sum_recordOccupation_eq_clock_of_index (records : Records s) (n : ℕ)
    (hn : firstAbsorptionIndex records = (n : WithTop ℕ)) :
    ∑ i, recordOccupation i records = recordClock n records := by
  simp_rw [recordOccupation_eq_sum_of_index records _ n hn]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have hnonzero := ((firstAbsorptionIndex_eq_iff records n).mp hn).2 k
    (Finset.mem_range.mp hk)
  rcases Fin.eq_zero_or_eq_succ (records k).2 with h | ⟨i, hi⟩
  · exact (hnonzero h).elim
  · simp [hi, Fin.succ_inj]

theorem sum_recordOccupation_eq_absorptionTime_of_index (records : Records s) (n : ℕ)
    (hn : firstAbsorptionIndex records = (n : WithTop ℕ))
    (hhold : ∀ k, 0 ≤ (records (k + 1)).1) :
    ∑ i, recordOccupation i records = (recordAbsorptionTime records).toReal :=
  (sum_recordOccupation_eq_clock_of_index records n hn).trans
    (recordAbsorptionTime_toReal_eq_clock records n hn hhold).symm

/-- All transient occupation times sum to the absorption time on the same records. -/
theorem canonicalRecords_sum_occupation_eq_absorptionTime (d : PhaseTypeData s) :
    ∀ᵐ records ∂d.canonicalRecords,
      ∑ i, recordOccupation i records = (recordAbsorptionTime records).toReal := by
  filter_upwards [d.canonicalRecords_firstAbsorptionIndex_ne_top_ae,
    d.canonicalRecords_holding_nonneg] with records hfinite hhold
  induction hindex : firstAbsorptionIndex records using WithTop.recTopCoe with
  | top => exact (hfinite hindex).elim
  | coe n => exact sum_recordOccupation_eq_absorptionTime_of_index records n hindex hhold

variable {n : ℕ}

/-- Occupation of the distinguished transient state, on the actual jump records. -/
noncomputable def recordOccupationZero (records : Records (n + 1)) : ℝ :=
  recordOccupation 0 records

/-- Occupation of all other transient states, on the same jump records. -/
noncomputable def recordOccupationRest (records : Records (n + 1)) : ℝ :=
  ∑ i : Fin n, recordOccupation i.succ records

theorem measurable_recordOccupationZero : Measurable (recordOccupationZero (n := n)) :=
  measurable_recordOccupation 0

theorem measurable_recordOccupationRest : Measurable (recordOccupationRest (n := n)) :=
  Finset.measurable_sum _ fun i _ ↦ measurable_recordOccupation i.succ

theorem sum_recordOccupation_eq_zero_add_rest (records : Records (n + 1)) :
    ∑ i, recordOccupation i records =
      recordOccupationZero records + recordOccupationRest records :=
  Fin.sum_univ_succ _

theorem canonicalRecords_occupationZero_nonneg (d : PhaseTypeData (n + 1)) :
    ∀ᵐ records ∂d.canonicalRecords, 0 ≤ recordOccupationZero records :=
  d.canonicalRecords_occupation_nonneg.mono fun _ h ↦ h 0

theorem canonicalRecords_occupationRest_nonneg (d : PhaseTypeData (n + 1)) :
    ∀ᵐ records ∂d.canonicalRecords, 0 ≤ recordOccupationRest records :=
  d.canonicalRecords_occupation_nonneg.mono fun _ h ↦
    Finset.sum_nonneg fun i _ ↦ h i.succ

/-- The distinguished occupation and its complement split the actual absorption time. -/
theorem canonicalRecords_absorptionTime_eq_occupationZero_add_rest
    (d : PhaseTypeData (n + 1)) :
    ∀ᵐ records ∂d.canonicalRecords,
      (recordAbsorptionTime records).toReal =
        recordOccupationZero records + recordOccupationRest records :=
  d.canonicalRecords_sum_occupation_eq_absorptionTime.mono fun records h ↦
    h.symm.trans (sum_recordOccupation_eq_zero_add_rest records)

end SSPRK.PhaseTypeData
