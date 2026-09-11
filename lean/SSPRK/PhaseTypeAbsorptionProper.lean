import SSPRK.PhaseTypeEmbeddedChain
import SSPRK.PhaseTypeCanonicalRecords
import SSPRK.CanonicalStateMarginals

/-!
# Almost-sure absorption of canonical phase-type records

The transient block of the Q-matrix embedded chain is the matrix from
`PhaseTypeEmbeddedChain`. Its powers tend to zero, so the transient state mass
in the actual canonical record process tends to zero. Consequently the first
absorption index is finite almost surely.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace SSPRK
namespace PhaseTypeData

noncomputable section

/-- A single transient jump agrees with the real embedded transition matrix. -/
theorem qMatrix_embeddedDTMC_step_succ_succ {s : ℕ} (d : PhaseTypeData s)
    (i j : Fin s) :
    d.qMatrix.embeddedDTMC.step i.succ j.succ =
      ENNReal.ofReal (d.embeddedTransition i j) := by
  by_cases hij : i = j
  · subst j
    rw [d.qMatrix.embeddedDTMC_step_self_of_nonabsorbing
      (d.qMatrix_not_isAbsorbing_succ i)]
    simp
  · rw [d.embeddedDTMC_step_succ_succ hij, d.embeddedTransition_apply_of_ne hij]

/-- Starting from the absorbing state, every embedded-chain iterate stays there. -/
theorem qMatrix_embeddedDTMC_stepN_zero {s : ℕ} (d : PhaseTypeData s) (n : ℕ) :
    d.qMatrix.embeddedDTMC.stepN n 0 = PMF.pure 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (d.qMatrix.embeddedDTMC.stepN n 0).bind d.qMatrix.embeddedDTMC.step =
        PMF.pure 0
      rw [ih, PMF.pure_bind]
      apply PMF.ext
      intro y
      simp [d.embeddedDTMC_step_zero, PMF.pure_apply]

/-- The transient block of the `n`-step embedded Q-matrix chain is `R ^ n`. -/
theorem qMatrix_embeddedDTMC_stepN_succ_succ {s : ℕ} (d : PhaseTypeData s)
    (n : ℕ) (i j : Fin s) :
    d.qMatrix.embeddedDTMC.stepN n i.succ j.succ =
      ENNReal.ofReal ((d.embeddedTransition ^ n) i j) := by
  induction n generalizing i j with
  | zero =>
      simp only [Ripple.CTMC.DTMC.stepN, PMF.pure_apply, pow_zero, Matrix.one_apply]
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij, Ne.symm hij]
  | succ n ih =>
      rw [Ripple.CTMC.DTMC.stepN, PMF.bind_apply, tsum_fintype, Fin.sum_univ_succ]
      simp only [d.embeddedDTMC_step_zero, Fin.succ_ne_zero, if_false, mul_zero, zero_add]
      simp_rw [ih, d.qMatrix_embeddedDTMC_step_succ_succ]
      simp_rw [← ENNReal.ofReal_mul
        ((d.embeddedTransition_substochastic.pow n).nonneg i _)]
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · rw [pow_succ, Matrix.mul_apply]
      · intro k _
        exact mul_nonneg ((d.embeddedTransition_substochastic.pow n).nonneg i k)
          (d.embeddedTransition_nonneg k j)

/-- The embedded state PMF after `n` jumps, mixed with the actual initial PMF. -/
def embeddedLawN {s : ℕ} (d : PhaseTypeData s) (n : ℕ) : PMF (Fin (s + 1)) :=
  d.initialPMF.bind (d.qMatrix.embeddedDTMC.stepN n)

/-- A transient point mass in the mixed embedded law is the corresponding matrix product. -/
theorem embeddedLawN_succ {s : ℕ} (d : PhaseTypeData s) (n : ℕ) (j : Fin s) :
    d.embeddedLawN n j.succ =
      ENNReal.ofReal (Matrix.vecMul d.initial (d.embeddedTransition ^ n) j) := by
  rw [embeddedLawN, PMF.bind_apply, tsum_fintype, Fin.sum_univ_succ]
  rw [d.initialPMF_zero, d.qMatrix_embeddedDTMC_stepN_zero]
  simp only [PMF.pure_apply, Fin.succ_ne_zero, if_false, mul_zero, zero_add,
    d.initialPMF_succ]
  simp_rw [d.qMatrix_embeddedDTMC_stepN_succ_succ]
  simp_rw [← ENNReal.ofReal_mul (d.initial_nonneg _)]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · rfl
  · intro i _
    exact mul_nonneg (d.initial_nonneg i)
      ((d.embeddedTransition_substochastic.pow n).nonneg i j)

/-- The actual canonical-record state marginal is the mixed embedded-chain law. -/
theorem canonicalRecords_state_law {s : ℕ} (d : PhaseTypeData s) (n : ℕ) :
    d.canonicalRecords.map (fun records ↦ (records n).2) =
      (d.embeddedLawN n).toMeasure := by
  rw [canonicalRecords,
    Measure.map_sum (measurable_record_state (s := s) n).aemeasurable]
  simp only [Measure.map_smul]
  change Measure.sum (fun z ↦ d.initialPMF z • d.qMatrix.canonicalStateLaw z n) =
    (d.embeddedLawN n).toMeasure
  simp_rw [d.qMatrix.canonicalStateLaw_eq_stepN]
  apply Measure.ext_of_singleton
  intro y
  rw [Measure.sum_apply _ (MeasurableSet.singleton y)]
  simp only [Measure.smul_apply, PMF.toMeasure_apply_singleton _ _
    (MeasurableSet.singleton _), smul_eq_mul]
  rw [embeddedLawN, PMF.bind_apply]

/-- Total probability of still occupying a transient state after `n` jumps. -/
def embeddedSurvivalMass {s : ℕ} (d : PhaseTypeData s) (n : ℕ) : ℝ≥0∞ :=
  ∑ j : Fin s, d.embeddedLawN n j.succ

/-- The transient survival mass is the usual initial-row matrix-power expression. -/
theorem embeddedSurvivalMass_eq {s : ℕ} (d : PhaseTypeData s) (n : ℕ) :
    d.embeddedSurvivalMass n = ENNReal.ofReal
      (dotProduct d.initial ((d.embeddedTransition ^ n).mulVec (fun _ ↦ 1))) := by
  rw [embeddedSurvivalMass]
  simp_rw [d.embeddedLawN_succ]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    calc
      ∑ j, Matrix.vecMul d.initial (d.embeddedTransition ^ n) j =
          ∑ j, ∑ i, d.initial i * (d.embeddedTransition ^ n) i j := rfl
      _ = ∑ i, ∑ j, d.initial i * (d.embeddedTransition ^ n) i j := Finset.sum_comm
      _ = ∑ i, d.initial i * ∑ j, (d.embeddedTransition ^ n) i j := by
        simp only [Finset.mul_sum]
      _ = dotProduct d.initial ((d.embeddedTransition ^ n).mulVec (fun _ ↦ 1)) := by
        simp [dotProduct, Matrix.mulVec]
  · intro j _
    simp only [Matrix.vecMul, dotProduct]
    exact Finset.sum_nonneg fun i _ ↦
      mul_nonneg (d.initial_nonneg i)
        ((d.embeddedTransition_substochastic.pow n).nonneg i j)

/-- The real transient survival expression tends to zero. -/
theorem embeddedSurvivalReal_tendsto_zero {s : ℕ} (d : PhaseTypeData s) :
    Tendsto (fun n : ℕ ↦
      dotProduct d.initial ((d.embeddedTransition ^ n).mulVec (fun _ ↦ 1)))
      atTop (𝓝 0) := by
  simp only [dotProduct, Matrix.mulVec, mul_one]
  have hinner (i : Fin s) :
      Tendsto (fun n : ℕ ↦ ∑ j, (d.embeddedTransition ^ n) i j) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun j _ ↦
      tendsto_pi_nhds.mp (tendsto_pi_nhds.mp
        d.embeddedTransition_pow_tendsto_zero i) j)
  simpa using tendsto_finsetSum Finset.univ (fun i _ ↦
    tendsto_const_nhds.mul (hinner i))

/-- The probability of remaining in the transient block tends to zero. -/
theorem embeddedSurvivalMass_tendsto_zero {s : ℕ} (d : PhaseTypeData s) :
    Tendsto d.embeddedSurvivalMass atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ ↦ d.embeddedSurvivalMass n) atTop (𝓝 0)
  simp_rw [d.embeddedSurvivalMass_eq]
  simpa using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    d.embeddedSurvivalReal_tendsto_zero

/-- Survival in the canonical record process has the embedded-chain survival mass. -/
theorem canonicalRecords_state_ne_zero_measure {s : ℕ} (d : PhaseTypeData s) (n : ℕ) :
    d.canonicalRecords {records | (records n).2 ≠ 0} =
      d.embeddedSurvivalMass n := by
  let transient : Set (Fin (s + 1)) := {x | x ≠ 0}
  have htransient : MeasurableSet transient := by
    exact (MeasurableSet.singleton (0 : Fin (s + 1))).compl
  calc
    d.canonicalRecords {records | (records n).2 ≠ 0} =
        (d.canonicalRecords.map (fun records ↦ (records n).2)) transient := by
      rw [Measure.map_apply (measurable_record_state (s := s) n) htransient]
      rfl
    _ = (d.embeddedLawN n).toMeasure transient := by
      rw [d.canonicalRecords_state_law n]
    _ = ∑ j : Fin s, d.embeddedLawN n j.succ := by
      have hset : transient =
          (↑((Finset.univ : Finset (Fin (s + 1))).erase 0) : Set (Fin (s + 1))) := by
        ext x
        simp [transient]
      rw [hset, PMF.toMeasure_apply_finset]
      have hsplit := Finset.sum_erase_add Finset.univ (d.embeddedLawN n)
        (Finset.mem_univ (0 : Fin (s + 1)))
      rw [Fin.sum_univ_succ] at hsplit
      apply (ENNReal.add_right_inj (PMF.apply_ne_top (d.embeddedLawN n) 0)).mp
      simpa [add_comm] using hsplit
    _ = d.embeddedSurvivalMass n := rfl

/-- The actual canonical jump-record process reaches the absorbing state almost surely. -/
theorem canonicalRecords_firstAbsorptionIndex_ne_top_ae {s : ℕ} (d : PhaseTypeData s) :
    ∀ᵐ records ∂d.canonicalRecords,
      firstAbsorptionIndex records ≠ ⊤ := by
  let never : Set (Records s) := {records | firstAbsorptionIndex records = ⊤}
  have hle : ∀ n, d.canonicalRecords never ≤ d.embeddedSurvivalMass n := by
    intro n
    rw [← d.canonicalRecords_state_ne_zero_measure n]
    apply measure_mono
    intro records hrecords
    exact (firstAbsorptionIndex_eq_top_iff records).mp hrecords n
  have hzero : d.canonicalRecords never = 0 := by
    apply le_antisymm
    · exact le_of_tendsto_of_tendsto' tendsto_const_nhds
        d.embeddedSurvivalMass_tendsto_zero hle
    · exact bot_le
  rw [ae_iff]
  simpa only [never, Set.mem_setOf_eq, not_ne_iff] using hzero

end

end PhaseTypeData
end SSPRK
