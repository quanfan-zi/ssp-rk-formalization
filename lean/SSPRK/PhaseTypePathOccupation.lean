import SSPRK.PhaseTypePath
import SSPRK.PhaseTypeRecordOccupation
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Occupation as an integral along the actual continuous-time path

Every finite record horizon is partitioned into its half-open holding intervals.
The integral of a state's indicator on each interval is its holding time exactly
when that state is occupied. Almost-sure finite absorption then gives the stopped
occupation identity, including immediate absorption and zero-length intervals.
-/

open MeasureTheory Set
open scoped BigOperators

namespace SSPRK.PhaseTypeData

variable {s : ℕ}

/-- The real indicator that the actual path occupies transient state `i` at time `t`. -/
noncomputable def recordStateIndicator (i : Fin s) (records : Records s) : ℝ → ℝ :=
  {t | recordStateAt t records = i.succ}.indicator (fun _ ↦ 1)

theorem measurable_recordStateIndicator (i : Fin s) (records : Records s) :
    Measurable (recordStateIndicator i records) :=
  measurable_const.indicator
    (measurableSet_eq_fun (measurable_recordStateAt_time records) measurable_const)

/-- A path-state indicator is integrable on every bounded half-open time interval. -/
theorem integrableOn_recordStateIndicator (i : Fin s) (records : Records s) (a b : ℝ) :
    IntegrableOn (recordStateIndicator i records) (Ico a b) :=
  (integrableOn_const (C := (1 : ℝ)) (by simp [Real.volume_Ico])).indicator
    (measurableSet_eq_fun (measurable_recordStateAt_time records) measurable_const)

/-- On one sojourn, the state indicator integrates to the corresponding holding time. -/
theorem integral_recordStateIndicator_sojourn (i : Fin s) (records : Records s)
    (hhold : ∀ n, 0 ≤ (records (n + 1)).1) (k : ℕ) :
    (∫ t in Ico (recordClock k records) (recordClock (k + 1) records),
      recordStateIndicator i records t) =
        if (records k).2 = i.succ then (records (k + 1)).1 else 0 := by
  calc
    _ = ∫ _ in Ico (recordClock k records) (recordClock (k + 1) records),
        (if (records k).2 = i.succ then (1 : ℝ) else 0) := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro t ht
      simp [recordStateIndicator, recordStateAt_eq_of_sojourn records hhold k t ht,
        Set.indicator]
    _ = _ := by
      rw [setIntegral_const,
        Real.volume_real_Ico_of_le ((recordClock_monotone records hhold) (Nat.le_succ k))]
      split_ifs <;> simp [recordClock_succ]

/-- A finite-horizon occupation sum equals the integral along the actual path. -/
theorem recordOccupationUntil_eq_integral (i : Fin s) (records : Records s)
    (hhold : ∀ n, 0 ≤ (records (n + 1)).1) (k : ℕ) :
    recordOccupationUntil i k records =
      ∫ t in Ico 0 (recordClock k records), recordStateIndicator i records t := by
  induction k with
  | zero => simp [recordOccupationUntil]
  | succ k ih =>
      have hunion : Ico 0 (recordClock (k + 1) records) =
          Ico 0 (recordClock k records) ∪
            Ico (recordClock k records) (recordClock (k + 1) records) :=
        (Ico_union_Ico_eq_Ico (recordClock_nonneg records hhold k)
          ((recordClock_monotone records hhold) (Nat.le_succ k))).symm
      rw [hunion, setIntegral_union Ico_disjoint_Ico_same measurableSet_Ico
        (integrableOn_recordStateIndicator i records _ _)
        (integrableOn_recordStateIndicator i records _ _),
        integral_recordStateIndicator_sojourn i records hhold, ← ih]
      exact Finset.sum_range_succ _ k

/-- A finite absorption index turns the pathwise finite-horizon identity into a stopped one. -/
theorem recordOccupation_eq_integral_of_index (i : Fin s) (records : Records s)
    (hhold : ∀ n, 0 ≤ (records (n + 1)).1) (k : ℕ)
    (hindex : firstAbsorptionIndex records = (k : WithTop ℕ)) :
    recordOccupation i records =
      ∫ t in Ico 0 (recordAbsorptionTime records).toReal, recordStateIndicator i records t := by
  rw [recordAbsorptionTime_toReal_eq_clock records k hindex hhold,
    recordOccupation, recordAbsorptionCount_eq_of_index records k hindex]
  exact recordOccupationUntil_eq_integral i records hhold k

/-- Each actual occupation variable is almost surely its stopped path-state indicator integral. -/
theorem canonicalRecords_occupation_eq_pathIntegral (d : PhaseTypeData s) :
    ∀ᵐ records ∂d.canonicalRecords, ∀ i,
      recordOccupation i records =
        ∫ t in Ico 0 (recordAbsorptionTime records).toReal,
          recordStateIndicator i records t := by
  filter_upwards [d.canonicalRecords_firstAbsorptionIndex_ne_top_ae,
    d.canonicalRecords_holding_nonneg] with records hfinite hhold
  induction hindex : firstAbsorptionIndex records using WithTop.recTopCoe with
  | top => exact (hfinite hindex).elim
  | coe k => exact fun i ↦ recordOccupation_eq_integral_of_index i records hhold k hindex

variable {n : ℕ}

/-- The actual path occupies a transient state other than the distinguished state. -/
noncomputable def recordRestIndicator (records : Records (n + 1)) : ℝ → ℝ :=
  {t | recordStateAt t records ≠ 0 ∧
    recordStateAt t records ≠ (0 : Fin (n + 1)).succ}.indicator (fun _ ↦ 1)

theorem sum_recordStateIndicator_eq_rest (records : Records (n + 1)) (t : ℝ) :
    ∑ i : Fin n, recordStateIndicator i.succ records t = recordRestIndicator records t := by
  rcases Fin.eq_zero_or_eq_succ (recordStateAt t records) with hz | ⟨j, hj⟩
  · simp [recordStateIndicator, recordRestIndicator, Set.indicator, hz, eq_comm]
  · rcases Fin.eq_zero_or_eq_succ j with hjzero | ⟨i, hi⟩
    · simp [recordStateIndicator, recordRestIndicator, Set.indicator, hj, hjzero,
        eq_comm, Fin.succ_succ_ne_one]
    · simp [recordStateIndicator, recordRestIndicator, Set.indicator, hj, hi,
        Fin.succ_succ_ne_one]

theorem integrableOn_recordRestIndicator (records : Records (n + 1)) (a b : ℝ) :
    IntegrableOn (recordRestIndicator records) (Ico a b) := by
  have hsum := integrable_finsetSum Finset.univ
    (fun (i : Fin n) _ ↦ integrableOn_recordStateIndicator i.succ records a b)
  simpa only [sum_recordStateIndicator_eq_rest] using hsum

/-- The distinguished occupation is the time integral of its actual path-state indicator. -/
theorem canonicalRecords_occupationZero_eq_pathIntegral (d : PhaseTypeData (n + 1)) :
    ∀ᵐ records ∂d.canonicalRecords,
      recordOccupationZero records =
        ∫ t in Ico 0 (recordAbsorptionTime records).toReal,
          recordStateIndicator 0 records t :=
  d.canonicalRecords_occupation_eq_pathIntegral.mono fun _ h ↦ h 0

/-- The complementary occupation integrates the indicator of the other transient states. -/
theorem canonicalRecords_occupationRest_eq_pathIntegral (d : PhaseTypeData (n + 1)) :
    ∀ᵐ records ∂d.canonicalRecords,
      recordOccupationRest records =
        ∫ t in Ico 0 (recordAbsorptionTime records).toReal, recordRestIndicator records t := by
  filter_upwards [d.canonicalRecords_occupation_eq_pathIntegral] with records h
  simp_rw [recordOccupationRest, h]
  rw [← integral_finsetSum Finset.univ
    (fun (i : Fin n) _ ↦ integrableOn_recordStateIndicator i.succ records _ _)]
  simp only [sum_recordStateIndicator_eq_rest]

/-- Both terms of the absorption-time split are integrals along this same path. -/
theorem canonicalRecords_absorptionTime_eq_pathIntegrals (d : PhaseTypeData (n + 1)) :
    ∀ᵐ records ∂d.canonicalRecords,
      (recordAbsorptionTime records).toReal =
        (∫ t in Ico 0 (recordAbsorptionTime records).toReal, recordStateIndicator 0 records t) +
        (∫ t in Ico 0 (recordAbsorptionTime records).toReal, recordRestIndicator records t) := by
  filter_upwards [d.canonicalRecords_absorptionTime_eq_occupationZero_add_rest,
    d.canonicalRecords_occupationZero_eq_pathIntegral,
    d.canonicalRecords_occupationRest_eq_pathIntegral] with records hsplit hzero hrest
  exact hsplit.trans (congrArg₂ (· + ·) hzero hrest)

end SSPRK.PhaseTypeData
