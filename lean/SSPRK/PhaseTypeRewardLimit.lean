import SSPRK.PhaseTypeRecordOccupation
import SSPRK.PhaseTypeRecordRewardHarmonic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Terminal rewards on absorbing records

A state-dependent reward is the corresponding weighted sum of actual occupation times.
It is the eventual value of the finite reward clocks.
-/

open MeasureTheory Filter
open scoped Topology

namespace SSPRK.PhaseTypeData

variable {s : ℕ}

/-- Total reward accumulated before absorption, as a weighted occupation sum. -/
noncomputable def recordRewardTotal (c : Fin (s + 1) → ℝ) (records : Records s) : ℝ :=
  ∑ i, c i.succ * recordOccupation i records

theorem measurable_recordRewardTotal (c : Fin (s + 1) → ℝ) :
    Measurable (recordRewardTotal c) := by
  exact Finset.measurable_sum _ fun i _ ↦ measurable_const.mul (measurable_recordOccupation i)

/-- A terminal reward equals its finite holding-time sum at the absorption index. -/
theorem recordRewardTotal_eq_sum_of_index (c : Fin (s + 1) → ℝ)
    (records : Records s) (n : ℕ) (hn : firstAbsorptionIndex records = (n : WithTop ℕ)) :
    recordRewardTotal c records =
      ∑ k ∈ Finset.range n, c (records k).2 * (records (k + 1)).1 := by
  simp only [recordRewardTotal, recordOccupation_eq_sum_of_index records _ n hn,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have hnonzero := ((firstAbsorptionIndex_eq_iff records n).mp hn).2 k
    (Finset.mem_range.mp hk)
  rcases Fin.eq_zero_or_eq_succ (records k).2 with h | ⟨i, hi⟩
  · exact (hnonzero h).elim
  · simp [hi, Fin.succ_inj]

/-- After absorption all later holding rewards vanish. -/
theorem recordRewardClock_eq_of_holding_zero (c : Fin (s + 1) → ℝ)
    (records : Records s) (k n : ℕ) (hkn : k ≤ n)
    (hzero : ∀ m, k ≤ m → (records (m + 1)).1 = 0) :
    recordRewardClock c n records = recordRewardClock c k records := by
  induction n, hkn using Nat.le_induction with
  | base => rfl
  | succ n hkn ih => rw [recordRewardClock_succ, hzero n hkn, mul_zero, add_zero, ih]

/-- Finite reward clocks eventually equal the terminal reward, with the state absorbed. -/
theorem canonicalRecords_rewardClock_eventually_terminal (d : PhaseTypeData s)
    (c : Fin (s + 1) → ℝ) :
    ∀ᵐ records ∂d.canonicalRecords, ∀ᶠ n in atTop,
      recordRewardClock c n records = recordRewardTotal c records ∧ (records n).2 = 0 := by
  filter_upwards [d.canonicalRecords_firstAbsorptionIndex_ne_top_ae,
    d.canonicalRecords_zero_persistent] with records hfinite hpersist
  induction hindex : firstAbsorptionIndex records using WithTop.recTopCoe with
  | top => exact (hfinite hindex).elim
  | coe k =>
      filter_upwards [eventually_ge_atTop k] with n hkn
      have hz := ((firstAbsorptionIndex_eq_iff records k).mp hindex).1
      refine ⟨?_, (hpersist k n hkn hz).1⟩
      exact (recordRewardClock_eq_of_holding_zero c records k n hkn
        (fun m hkm ↦ (hpersist k m hkm hz).2)).trans
        (recordRewardTotal_eq_sum_of_index c records k hindex).symm

/-- Bounded reward observables converge in expectation to their terminal Laplace kernel. -/
theorem tendsto_integral_recordRewardHarmonicIntegrand (d : PhaseTypeData s)
    {c f : Fin (s + 1) → ℝ} (hc : ∀ x, 0 ≤ c x)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_le_one : ∀ x, f x ≤ 1) (hfzero : f 0 = 1) :
    Tendsto (fun n ↦ ∫ records, recordRewardHarmonicIntegrand c f n records
      ∂d.canonicalRecords) atTop
      (𝓝 (∫ records, Real.exp (-recordRewardTotal c records) ∂d.canonicalRecords)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ))
  · exact fun n ↦ (measurable_recordRewardHarmonicIntegrand c f n).aestronglyMeasurable
  · exact integrable_const 1
  · intro n
    filter_upwards [d.canonicalRecords_rewardClock_nonneg hc] with records hnonneg
    have hb := recordRewardHarmonicIntegrand_mem_unitInterval hf_nonneg hf_le_one (hnonneg n)
    rw [Real.norm_of_nonneg hb.1]
    exact hb.2
  · filter_upwards [d.canonicalRecords_rewardClock_eventually_terminal c]
      with records hterminal
    apply tendsto_const_nhds.congr'
    exact hterminal.mono fun n hn ↦ by
      simp only [recordRewardHarmonicIntegrand, hn.1, hn.2, hfzero, mul_one]

/-- A bounded one-step reward-harmonic certificate identifies the terminal reward transform. -/
theorem integral_exp_neg_recordRewardTotal (d : PhaseTypeData s)
    {c f : Fin (s + 1) → ℝ} (hc : ∀ x, 0 ≤ c x)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_le_one : ∀ x, f x ≤ 1) (hfzero : f 0 = 1)
    (hharmonic : ∀ x,
      (∫ record : ℝ × Fin (s + 1), Real.exp (-(c x) * record.1) * f record.2
        ∂d.qMatrix.jumpHoldStepMeasureTotal x) = f x) :
    (∫ records, Real.exp (-recordRewardTotal c records) ∂d.canonicalRecords) =
      ∫ x, f x ∂d.initialMeasure := by
  have ht := d.tendsto_integral_recordRewardHarmonicIntegrand hc hf_nonneg hf_le_one hfzero
  simp only [d.integral_recordRewardHarmonicIntegrand_eq_initial hc
    hf_nonneg hf_le_one hharmonic] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

end SSPRK.PhaseTypeData
