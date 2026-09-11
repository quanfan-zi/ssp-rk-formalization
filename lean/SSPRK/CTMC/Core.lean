/-
Derived from pcbcos/Ripple contributors.
Upstream source: Ripple/CTMC/CTMC.lean
Upstream commit: 83d6a77319d1bbb9bd397f9613244d396dc48583
License: Apache-2.0; see repository-root licenses/Ripple-Apache-2.0.txt.
Modifications: retained the project dependency closure through the one-step Markov kernel,
changed the DTMC import to the local extraction, and omitted the transition semigroup and
later code.
-/

/-
  Ripple.CTMC.CTMC — Continuous-Time Markov Chain Foundation

  This bounded extraction defines finite-state Q-matrices, the embedded DTMC,
  exponential holding times, and the one-step jump-and-hold Markov kernel.
-/

import SSPRK.CTMC.DTMC
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open scoped ENNReal

namespace Ripple.CTMC

variable {S : Type*} [Fintype S] [DecidableEq S]
/-- A Q-matrix (infinitesimal generator) for a finite-state CTMC.
`q s t` is the rate of transitioning from s to t (for s ≠ t).
The diagonal satisfies q(s,s) = -Σ_{t≠s} q(s,t). -/
structure QMatrix (S : Type*) [Fintype S] [DecidableEq S] where
  /-- Off-diagonal transition rates. -/
  rate : S → S → ℝ
  /-- Off-diagonal rates are nonneg. -/
  rate_nonneg : ∀ s t, s ≠ t → 0 ≤ rate s t
  /-- Diagonal is minus the sum of off-diagonal rates. -/
  rate_diag : ∀ s, rate s s = -∑ t ∈ Finset.univ.filter (· ≠ s), rate s t

/-- Total exit rate from state s. -/
noncomputable def QMatrix.exitRate (Q : QMatrix S) (s : S) : ℝ :=
  ∑ t ∈ Finset.univ.filter (· ≠ s), Q.rate s t

/-- Exit rate is nonneg. -/
theorem QMatrix.exitRate_nonneg (Q : QMatrix S) (s : S) :
    0 ≤ Q.exitRate s :=
  Finset.sum_nonneg fun t ht => Q.rate_nonneg s t (Finset.mem_filter.mp ht).2.symm

/-- Diagonal entry equals negative exit rate. -/
theorem QMatrix.diag_eq_neg_exitRate (Q : QMatrix S) (s : S) :
    Q.rate s s = -Q.exitRate s :=
  Q.rate_diag s

/-- A state is absorbing if its exit rate is zero. -/
def QMatrix.IsAbsorbing (Q : QMatrix S) (s : S) : Prop :=
  Q.exitRate s = 0

/-- Normalized jump probability: q(s,t)/exitRate(s) for s ≠ t, 0 for s = t.
When the exit rate is zero (absorbing state), this returns 0 everywhere. -/
noncomputable def QMatrix.jumpProb (Q : QMatrix S) (s t : S) : ℝ≥0∞ :=
  if s = t then 0
  else ENNReal.ofReal (Q.rate s t / Q.exitRate s)

/-- Jump probabilities sum to 1 for non-absorbing states. -/
theorem QMatrix.jumpProb_sum (Q : QMatrix S) (s : S) (h : Q.exitRate s ≠ 0) :
    ∑ t, Q.jumpProb s t = 1 := by
  have h_pos : 0 < Q.exitRate s := lt_of_le_of_ne (Q.exitRate_nonneg s) (Ne.symm h)
  simp only [jumpProb]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ s), if_pos rfl, zero_add]
  rw [Finset.sum_congr rfl (fun t ht =>
    if_neg (Finset.ne_of_mem_erase ht).symm)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun t ht => div_nonneg
    (Q.rate_nonneg s t (Finset.ne_of_mem_erase ht).symm)
    (le_of_lt h_pos))]
  rw [← Finset.sum_div]
  have : ∑ t ∈ Finset.univ.erase s, Q.rate s t = Q.exitRate s := by
    rw [exitRate, ← Finset.filter_ne']
  rw [this, div_self (ne_of_gt h_pos), ENNReal.ofReal_one]

/-- The embedded DTMC: jump chain of the CTMC.
For non-absorbing states, jumps with probability q(s,t)/exitRate(s).
For absorbing states, stays put. -/
noncomputable def QMatrix.embeddedDTMC (Q : QMatrix S) [Countable S] :
    DTMC S where
  step s :=
    if h : Q.exitRate s = 0 then
      PMF.pure s
    else
      PMF.ofFintype (Q.jumpProb s) (Q.jumpProb_sum s h)

/-- Jump probability from s to itself is always 0. -/
theorem QMatrix.jumpProb_self (Q : QMatrix S) (s : S) :
    Q.jumpProb s s = 0 := by
  simp [jumpProb]

/-- For non-absorbing states, the embedded DTMC step equals jumpProb. -/
theorem QMatrix.embeddedDTMC_step_of_nonabsorbing (Q : QMatrix S) [Countable S]
    {s : S} (h : ¬Q.IsAbsorbing s) (t : S) :
    Q.embeddedDTMC.step s t = Q.jumpProb s t := by
  have hne : Q.exitRate s ≠ 0 := h
  simp only [embeddedDTMC, dif_neg hne, PMF.ofFintype_apply]

/-- For absorbing states, the embedded DTMC stays put. -/
theorem QMatrix.embeddedDTMC_step_of_absorbing (Q : QMatrix S) [Countable S]
    {s : S} (h : Q.IsAbsorbing s) (t : S) :
    Q.embeddedDTMC.step s t = if t = s then 1 else 0 := by
  simp only [embeddedDTMC, IsAbsorbing] at h ⊢
  simp [h, PMF.pure_apply]

/-- The embedded jump chain has no self-jump from a non-absorbing state. -/
theorem QMatrix.embeddedDTMC_step_self_of_nonabsorbing (Q : QMatrix S) [Countable S]
    {s : S} (h : ¬Q.IsAbsorbing s) :
    Q.embeddedDTMC.step s s = 0 := by
  rw [Q.embeddedDTMC_step_of_nonabsorbing h s, Q.jumpProb_self]

/-- The embedded jump-chain row as a probability measure.  This is the
measure-valued form used by kernel/product-measure constructions. -/
noncomputable def QMatrix.embeddedStepMeasure (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] (s : S) : MeasureTheory.Measure S :=
  (Q.embeddedDTMC.step s).toMeasure

/-- The embedded jump-chain row measure is a probability measure. -/
theorem QMatrix.isProbabilityMeasure_embeddedStepMeasure (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] (s : S) :
    MeasureTheory.IsProbabilityMeasure (Q.embeddedStepMeasure s) := by
  dsimp [embeddedStepMeasure]
  infer_instance

/-- Singleton masses of the embedded row measure recover the embedded DTMC
probabilities. -/
theorem QMatrix.embeddedStepMeasure_singleton (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (s t : S) :
    Q.embeddedStepMeasure s {t} = Q.embeddedDTMC.step s t := by
  simp [embeddedStepMeasure]

/-- Expectation against the embedded jump-chain row is the finite PMF sum. -/
theorem QMatrix.integral_embeddedStepMeasure_eq_sum (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    {s : S} (h : ¬Q.IsAbsorbing s) (f : S → ℝ) :
    ∫ t, f t ∂Q.embeddedStepMeasure s =
      ∑ t, (Q.jumpProb s t).toReal * f t := by
  rw [QMatrix.embeddedStepMeasure]
  rw [PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [Q.embeddedDTMC_step_of_nonabsorbing h t]
  simp

/-- Multiplying the embedded jump expectation by the exit rate recovers the
off-diagonal generator-weighted sum. -/
theorem QMatrix.exitRate_mul_integral_embeddedStepMeasure_eq_sum_rate
    (Q : QMatrix S) [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    {s : S} (h : ¬Q.IsAbsorbing s) (f : S → ℝ) :
    Q.exitRate s * (∫ t, f t ∂Q.embeddedStepMeasure s) =
      ∑ t ∈ Finset.univ.filter (fun t => t ≠ s), Q.rate s t * f t := by
  have hexit_pos : 0 < Q.exitRate s :=
    lt_of_le_of_ne (Q.exitRate_nonneg s) (Ne.symm h)
  rw [Q.integral_embeddedStepMeasure_eq_sum h f]
  rw [Finset.mul_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _ht
  by_cases hts : t ≠ s
  · have hst : s ≠ t := Ne.symm hts
    rw [if_pos hts]
    rw [QMatrix.jumpProb, if_neg hst]
    rw [ENNReal.toReal_ofReal]
    · field_simp [ne_of_gt hexit_pos]
    · exact div_nonneg (Q.rate_nonneg s t hst) (le_of_lt hexit_pos)
  · rw [if_neg hts]
    have hst_eq : s = t := (not_ne_iff.mp hts).symm
    rw [QMatrix.jumpProb, if_pos hst_eq]
    simp

/-- A non-absorbing embedded row puts zero mass on staying at the current
state. -/
theorem QMatrix.embeddedStepMeasure_singleton_self_of_nonabsorbing
    (Q : QMatrix S) [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    {s : S} (h : ¬Q.IsAbsorbing s) :
    Q.embeddedStepMeasure s {s} = 0 := by
  rw [Q.embeddedStepMeasure_singleton]
  exact Q.embeddedDTMC_step_self_of_nonabsorbing h

/-- A non-absorbing embedded jump-chain sample differs from the current state
almost surely. -/
theorem QMatrix.embeddedStepMeasure_ne_self_ae_of_nonabsorbing
    (Q : QMatrix S) [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    {s : S} (h : ¬Q.IsAbsorbing s) :
    ∀ᵐ u ∂Q.embeddedStepMeasure s, u ≠ s := by
  have hzero := Q.embeddedStepMeasure_singleton_self_of_nonabsorbing h
  have hnot : ∀ᵐ u ∂Q.embeddedStepMeasure s, u ∉ ({s} : Set S) :=
    MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hzero
  filter_upwards [hnot] with u hu
  simpa using hu

/-! ## Holding-time law -/

/-- A non-absorbing state has strictly positive exit rate. -/
theorem QMatrix.exitRate_pos_of_nonabsorbing (Q : QMatrix S) {s : S}
    (h : ¬Q.IsAbsorbing s) :
    0 < Q.exitRate s :=
  lt_of_le_of_ne (Q.exitRate_nonneg s) (Ne.symm h)

/-- Exponential holding-time law at a non-absorbing state.  Absorbing states
are deliberately excluded: in the jump-and-hold construction they do not have
a next finite holding time. -/
noncomputable def QMatrix.holdingTimeMeasure (Q : QMatrix S) {s : S}
    (_h : ¬Q.IsAbsorbing s) : MeasureTheory.Measure ℝ :=
  ProbabilityTheory.expMeasure (Q.exitRate s)

/-- The non-absorbing holding-time law is a probability measure. -/
theorem QMatrix.isProbabilityMeasure_holdingTimeMeasure (Q : QMatrix S) {s : S}
    (h : ¬Q.IsAbsorbing s) :
    MeasureTheory.IsProbabilityMeasure (Q.holdingTimeMeasure h) :=
  ProbabilityTheory.isProbabilityMeasure_expMeasure (Q.exitRate_pos_of_nonabsorbing h)

/-- CDF of the non-absorbing holding-time law. -/
theorem QMatrix.cdf_holdingTimeMeasure_eq (Q : QMatrix S) {s : S}
    (h : ¬Q.IsAbsorbing s) (t : ℝ) :
    ProbabilityTheory.cdf (Q.holdingTimeMeasure h) t =
      if 0 ≤ t then 1 - Real.exp (-(Q.exitRate s * t)) else 0 :=
  ProbabilityTheory.cdf_expMeasure_eq (Q.exitRate_pos_of_nonabsorbing h) t

/-- A non-absorbing exponential holding-time law assigns zero mass to
non-positive times. -/
theorem QMatrix.holdingTimeMeasure_Iic_zero (Q : QMatrix S) {s : S}
    (h : ¬Q.IsAbsorbing s) :
    Q.holdingTimeMeasure h (Set.Iic 0) = 0 := by
  letI := Q.isProbabilityMeasure_holdingTimeMeasure h
  have hcdf := Q.cdf_holdingTimeMeasure_eq h 0
  have hreal : (Q.holdingTimeMeasure h).real (Set.Iic 0) = 0 := by
    rw [← ProbabilityTheory.cdf_eq_real (Q.holdingTimeMeasure h) 0]
    simpa using hcdf
  exact (MeasureTheory.measureReal_eq_zero_iff).mp hreal

/-- A non-absorbing exponential holding-time sample is positive almost surely. -/
theorem QMatrix.holdingTimeMeasure_pos_ae (Q : QMatrix S) {s : S}
    (h : ¬Q.IsAbsorbing s) :
    ∀ᵐ t ∂Q.holdingTimeMeasure h, 0 < t := by
  have hzero := Q.holdingTimeMeasure_Iic_zero h
  have hnot : ∀ᵐ t ∂Q.holdingTimeMeasure h, t ∉ Set.Iic 0 :=
    MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hzero
  filter_upwards [hnot] with t ht
  exact lt_of_not_ge ht

/-- One-step jump-hold law from a non-absorbing state: exponential holding
time paired independently with the embedded next-state row. -/
noncomputable def QMatrix.jumpHoldStepMeasure (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] {s : S} (h : ¬Q.IsAbsorbing s) :
    MeasureTheory.Measure (ℝ × S) :=
  (Q.holdingTimeMeasure h).prod (Q.embeddedStepMeasure s)

/-- The one-step jump-hold law is a probability measure. -/
theorem QMatrix.isProbabilityMeasure_jumpHoldStepMeasure (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] {s : S} (h : ¬Q.IsAbsorbing s) :
    MeasureTheory.IsProbabilityMeasure (Q.jumpHoldStepMeasure h) := by
  letI := Q.isProbabilityMeasure_holdingTimeMeasure h
  letI := Q.isProbabilityMeasure_embeddedStepMeasure s
  dsimp [jumpHoldStepMeasure]
  infer_instance

/-- The holding-time marginal of the non-absorbing one-step jump-hold law is
the exponential holding-time law. -/
theorem QMatrix.jumpHoldStepMeasure_map_fst (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] {s : S} (h : ¬Q.IsAbsorbing s) :
    (Q.jumpHoldStepMeasure h).map Prod.fst = Q.holdingTimeMeasure h := by
  unfold jumpHoldStepMeasure
  letI := Q.isProbabilityMeasure_embeddedStepMeasure s
  simp

/-- The next-state marginal of the non-absorbing one-step jump-hold law is
the embedded jump-chain row measure. -/
theorem QMatrix.jumpHoldStepMeasure_map_snd (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] {s : S} (h : ¬Q.IsAbsorbing s) :
    (Q.jumpHoldStepMeasure h).map Prod.snd = Q.embeddedStepMeasure s := by
  unfold jumpHoldStepMeasure
  letI := Q.isProbabilityMeasure_holdingTimeMeasure h
  simp

/-- The sampled holding time in a non-absorbing jump-hold step is positive
almost surely. -/
theorem QMatrix.jumpHoldStepMeasure_holdingTime_pos_ae (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] {s : S} (h : ¬Q.IsAbsorbing s) :
    ∀ᵐ r ∂Q.jumpHoldStepMeasure h, 0 < r.1 := by
  have hpos := Q.holdingTimeMeasure_pos_ae h
  rw [← Q.jumpHoldStepMeasure_map_fst h] at hpos
  exact MeasureTheory.ae_of_ae_map measurable_fst.aemeasurable hpos

/-- The sampled next state in a non-absorbing jump-hold step differs from the
current state almost surely. -/
theorem QMatrix.jumpHoldStepMeasure_next_ne_self_ae (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    {s : S} (h : ¬Q.IsAbsorbing s) :
    ∀ᵐ r ∂Q.jumpHoldStepMeasure h, r.2 ≠ s := by
  have hne := Q.embeddedStepMeasure_ne_self_ae_of_nonabsorbing h
  rw [← Q.jumpHoldStepMeasure_map_snd h] at hne
  exact MeasureTheory.ae_of_ae_map measurable_snd.aemeasurable hne

/-- Total one-step jump-hold law.  Non-absorbing states use the genuine
exponential-hold/jump product law; absorbing states are represented by the
terminal marker `(0, s)`. -/
noncomputable def QMatrix.jumpHoldStepMeasureTotal (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] (s : S) : MeasureTheory.Measure (ℝ × S) :=
  by
    classical
    exact if h : Q.IsAbsorbing s then MeasureTheory.Measure.dirac (0, s)
      else Q.jumpHoldStepMeasure h

/-- At an absorbing state, the total one-step jump-hold law is the terminal
marker. -/
theorem QMatrix.jumpHoldStepMeasureTotal_of_absorbing (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] {s : S} (h : Q.IsAbsorbing s) :
    Q.jumpHoldStepMeasureTotal s = MeasureTheory.Measure.dirac (0, s) := by
  classical
  simp [jumpHoldStepMeasureTotal, h]

/-- At a non-absorbing state, the total one-step jump-hold law is the genuine
one-step product law. -/
theorem QMatrix.jumpHoldStepMeasureTotal_of_nonabsorbing (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] {s : S} (h : ¬Q.IsAbsorbing s) :
    Q.jumpHoldStepMeasureTotal s = Q.jumpHoldStepMeasure h := by
  classical
  simp [jumpHoldStepMeasureTotal, h]

/-- The total one-step jump-hold law is always a probability measure. -/
theorem QMatrix.isProbabilityMeasure_jumpHoldStepMeasureTotal (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] (s : S) :
    MeasureTheory.IsProbabilityMeasure (Q.jumpHoldStepMeasureTotal s) := by
  by_cases h : Q.IsAbsorbing s
  · rw [Q.jumpHoldStepMeasureTotal_of_absorbing h]
    infer_instance
  · rw [Q.jumpHoldStepMeasureTotal_of_nonabsorbing h]
    exact Q.isProbabilityMeasure_jumpHoldStepMeasure h

/-- The total one-step jump-hold law as a Markov kernel from current state to
the next hold/jump record. -/
noncomputable def QMatrix.jumpHoldStepKernel (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S] :
    ProbabilityTheory.Kernel S (ℝ × S) where
  toFun s := Q.jumpHoldStepMeasureTotal s
  measurable' :=
    MeasureTheory.Measure.measurable_of_measurable_coe _ fun A _hA =>
      measurable_of_countable fun s => Q.jumpHoldStepMeasureTotal s A

/-- Applying the total jump-hold kernel recovers the total one-step law. -/
theorem QMatrix.jumpHoldStepKernel_apply (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S] (s : S) :
    Q.jumpHoldStepKernel s = Q.jumpHoldStepMeasureTotal s :=
  rfl

/-- The total jump-hold kernel is Markov. -/
theorem QMatrix.isMarkovKernel_jumpHoldStepKernel (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S] :
    ProbabilityTheory.IsMarkovKernel Q.jumpHoldStepKernel where
  isProbabilityMeasure s := Q.isProbabilityMeasure_jumpHoldStepMeasureTotal s

end Ripple.CTMC
