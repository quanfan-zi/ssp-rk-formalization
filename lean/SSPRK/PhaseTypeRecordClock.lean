import SSPRK.PhaseTypeCanonicalRecords

/-!
# The clock read from canonical jump records

The clock at step `n` counts precisely the holding times in records `1, ..., n`.
After a finite absorption index it is constant. Under almost-sure absorption it
therefore converges to the real value of the extended absorption time.
-/

open MeasureTheory Filter
open scoped Topology

namespace SSPRK.PhaseTypeData

variable {s : ℕ}

/-- Elapsed holding time through record `n`, with initial clock zero. -/
noncomputable def recordClock (n : ℕ) (records : Records s) : ℝ :=
  ∑ k ∈ Finset.range n, (records (k + 1)).1

/-- Each finite record clock is measurable. -/
theorem measurable_recordClock (n : ℕ) : Measurable (recordClock (s := s) n) := by
  unfold recordClock
  fun_prop

@[simp] theorem recordClock_zero (records : Records s) : recordClock 0 records = 0 := by
  simp [recordClock]

/-- The next clock value adds the holding time stored in the next record. -/
theorem recordClock_succ (n : ℕ) (records : Records s) :
    recordClock (n + 1) records = recordClock n records + (records (n + 1)).1 := by
  exact Finset.sum_range_succ _ n

/-- Nonnegative sampled holding times give nonnegative clock values. -/
theorem recordClock_nonneg (records : Records s)
    (hhold : ∀ n, 0 ≤ (records (n + 1)).1) (n : ℕ) : 0 ≤ recordClock n records :=
  Finset.sum_nonneg fun k _ ↦ hhold k

/-- Under the canonical record law every finite clock value is nonnegative. -/
theorem canonicalRecords_clock_nonneg (d : PhaseTypeData s) :
    ∀ᵐ records ∂d.canonicalRecords, ∀ n, 0 ≤ recordClock n records :=
  d.canonicalRecords_holding_nonneg.mono fun records hhold ↦ recordClock_nonneg records hhold

/-- A zero tail of holding times makes the record clock constant on that tail. -/
theorem recordClock_eq_of_holding_zero (records : Records s) (k n : ℕ)
    (hkn : k ≤ n) (hzero : ∀ m, k ≤ m → (records (m + 1)).1 = 0) :
    recordClock n records = recordClock k records := by
  induction n, hkn using Nat.le_induction with
  | base => rfl
  | succ n hkn ih => rw [recordClock_succ, hzero n hkn, add_zero, ih]

/-- Once the first absorbing record occurs, all later record clocks agree. -/
theorem canonicalRecords_clock_constant_after_absorption (d : PhaseTypeData s) :
    ∀ᵐ records ∂d.canonicalRecords, ∀ k : ℕ,
      firstAbsorptionIndex records = (k : WithTop ℕ) → ∀ n, k ≤ n →
        recordClock n records = recordClock k records := by
  filter_upwards [d.canonicalRecords_zero_persistent] with records hpersist
  intro k hk n hkn
  exact recordClock_eq_of_holding_zero records k n hkn fun m hkm ↦
    (hpersist k m hkm ((firstAbsorptionIndex_eq_iff records k).mp hk).1).2

/-- At a finite absorption index, the extended time is the real clock at that index. -/
theorem recordAbsorptionTime_toReal_eq_clock (records : Records s) (k : ℕ)
    (hk : firstAbsorptionIndex records = (k : WithTop ℕ))
    (hhold : ∀ n, 0 ≤ (records (n + 1)).1) :
    (recordAbsorptionTime records).toReal = recordClock k records := by
  rw [recordAbsorptionTime_eq_sum_of_index records k hk,
    ENNReal.toReal_sum (fun _ _ ↦ ENNReal.ofReal_ne_top)]
  exact Finset.sum_congr rfl fun n _ ↦ ENNReal.toReal_ofReal (hhold n)

/-- Almost-sure finite absorption makes the clocks eventually equal to the absorption time. -/
theorem canonicalRecords_clock_eventually_eq_absorptionTime (d : PhaseTypeData s)
    (hproper : ∀ᵐ records ∂d.canonicalRecords, firstAbsorptionIndex records ≠ ⊤) :
    ∀ᵐ records ∂d.canonicalRecords, ∀ᶠ n in atTop,
      recordClock n records = (recordAbsorptionTime records).toReal := by
  filter_upwards [hproper, d.canonicalRecords_clock_constant_after_absorption,
    d.canonicalRecords_holding_nonneg] with records hfinite hconstant hhold
  induction hindex : firstAbsorptionIndex records using WithTop.recTopCoe with
  | top => exact (hfinite hindex).elim
  | coe k =>
      filter_upwards [eventually_ge_atTop k] with n hn
      exact (hconstant k hindex n hn).trans
        (recordAbsorptionTime_toReal_eq_clock records k hindex hhold).symm

/-- Under almost-sure finite absorption, finite clocks converge to the absorption time. -/
theorem canonicalRecords_clock_tendsto_absorptionTime (d : PhaseTypeData s)
    (hproper : ∀ᵐ records ∂d.canonicalRecords, firstAbsorptionIndex records ≠ ⊤) :
    ∀ᵐ records ∂d.canonicalRecords,
      Tendsto (fun n ↦ recordClock n records) atTop
        (𝓝 (recordAbsorptionTime records).toReal) := by
  filter_upwards [d.canonicalRecords_clock_eventually_eq_absorptionTime hproper]
    with records hconstant
  apply tendsto_const_nhds.congr'
  filter_upwards [hconstant] with n hn
  exact hn.symm

/-- Under properness the clock has reached its limit and the recorded state is zero eventually. -/
theorem canonicalRecords_clock_state_eventually_absorbed (d : PhaseTypeData s)
    (hproper : ∀ᵐ records ∂d.canonicalRecords, firstAbsorptionIndex records ≠ ⊤) :
    ∀ᵐ records ∂d.canonicalRecords, ∀ᶠ n in atTop,
      recordClock n records = (recordAbsorptionTime records).toReal ∧ (records n).2 = 0 := by
  filter_upwards [d.canonicalRecords_clock_eventually_eq_absorptionTime hproper,
    hproper, d.canonicalRecords_zero_persistent] with records hclock hfinite hpersist
  induction hindex : firstAbsorptionIndex records using WithTop.recTopCoe with
  | top => exact (hfinite hindex).elim
  | coe k =>
      filter_upwards [hclock, eventually_ge_atTop k] with n hn hkn
      exact ⟨hn, (hpersist k n hkn ((firstAbsorptionIndex_eq_iff records k).mp hindex).1).1⟩

end SSPRK.PhaseTypeData
