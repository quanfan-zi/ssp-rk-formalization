import SSPRK.PhaseTypeDensity
import Ripple.CTMC.CTMC

/-!
# Finite CTMC semantics of phase-type data

This file adjoins an absorbing state `0` to the transient states of a phase-type
representation. A transient state `i` is represented by `i.succ`. The resulting
Q-matrix has transient block `generator` and absorption-rate column
`(-generator).mulVec 1`.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace SSPRK.PhaseTypeData

variable {s : ℕ} (d : PhaseTypeData s)

/-- Every diagonal entry of the transient transition matrix is strictly below one. -/
theorem transition_diag_lt_one (i : Fin s) : d.transition i i < 1 := by
  have hle : d.transition i i ≤ 1 := d.substochastic.entry_le_one i i
  apply lt_of_le_of_ne hle
  intro hdiag
  apply d.transient
  apply Matrix.det_eq_zero_of_row_eq_zero i
  intro j
  simp only [Matrix.sub_apply, Matrix.one_apply]
  by_cases hji : j = i
  · subst j
    simp [hdiag]
  · have hsum_ge : 1 ≤ ∑ k, d.transition i k := by
      simpa [hdiag] using
        Finset.single_le_sum (fun k _ ↦ d.substochastic.nonneg i k)
          (Finset.mem_univ i)
    have hsum : ∑ k, d.transition i k = 1 :=
      le_antisymm (d.substochastic.row_sum_le i) hsum_ge
    have hsplit := Finset.add_sum_erase Finset.univ (fun k ↦ d.transition i k)
      (Finset.mem_univ i)
    have herase : ∑ k ∈ Finset.univ.erase i, d.transition i k = 0 := by
      change d.transition i i + ∑ k ∈ Finset.univ.erase i, d.transition i k =
        ∑ k, d.transition i k at hsplit
      rw [hdiag, hsum] at hsplit
      linarith
    have hjmem : j ∈ Finset.univ.erase i :=
      Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
    have hle_zero : d.transition i j ≤ 0 := by
      calc
        d.transition i j ≤ ∑ k ∈ Finset.univ.erase i, d.transition i k :=
          Finset.single_le_sum (fun k _ ↦ d.substochastic.nonneg i k) hjmem
        _ = 0 := herase
    rw [if_neg (Ne.symm hji), sub_eq_zero]
    exact le_antisymm (d.substochastic.nonneg i j) hle_zero

/-- The diagonal entries of the transient generator are strictly negative. -/
theorem generator_diag_neg (i : Fin s) : d.generator i i < 0 := by
  rw [generator]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.one_apply,
    if_pos]
  exact mul_neg_of_pos_of_neg d.rate_pos (sub_neg.mpr (d.transition_diag_lt_one i))

/-- The off-diagonal entries of the transient generator are nonnegative. -/
theorem generator_nonneg_of_ne {i j : Fin s} (hij : i ≠ j) :
    0 ≤ d.generator i j := by
  simp [generator, hij, mul_nonneg d.rate_pos.le (d.substochastic.nonneg i j)]

/-- Rates on the phase-type state space, with `0` as the absorbing state. -/
noncomputable def qRate : Fin (s + 1) → Fin (s + 1) → ℝ :=
  Fin.cases (fun _ ↦ 0) fun i ↦
    Fin.cases ((-d.generator).mulVec (fun _ ↦ 1) i) fun j ↦ d.generator i j

@[simp]
theorem qRate_zero (t : Fin (s + 1)) : d.qRate 0 t = 0 := by
  simp [qRate]

@[simp]
theorem qRate_succ_zero (i : Fin s) :
    d.qRate i.succ 0 = (-d.generator).mulVec (fun _ ↦ 1) i := by
  simp [qRate]

@[simp]
theorem qRate_succ_succ (i j : Fin s) :
    d.qRate i.succ j.succ = d.generator i j := by
  simp [qRate]

private theorem qRate_row_sum_succ (i : Fin s) : ∑ t, d.qRate i.succ t = 0 := by
  rw [Fin.sum_univ_succ]
  simp only [qRate_succ_zero, qRate_succ_succ]
  have hneg : (-d.generator).mulVec (fun _ ↦ 1) i = -∑ j, d.generator i j := by
    simp [Matrix.mulVec, dotProduct, Finset.sum_neg_distrib]
  rw [hneg]
  ring

/-- The finite-state CTMC Q-matrix associated with the phase-type representation. -/
noncomputable def qMatrix : Ripple.CTMC.QMatrix (Fin (s + 1)) where
  rate := d.qRate
  rate_nonneg := by
    intro x y hxy
    induction x using Fin.cases with
    | zero => simp
    | succ i =>
      induction y using Fin.cases with
      | zero =>
          rw [qRate_succ_zero, d.neg_generator_mulVec_one]
          exact mul_nonneg d.rate_pos.le (d.exit_nonneg i)
      | succ j =>
          have hij : i ≠ j := by
            intro hij
            subst j
            exact hxy rfl
          exact d.generator_nonneg_of_ne hij
  rate_diag := by
    intro x
    induction x using Fin.cases with
    | zero => simp
    | succ i =>
      rw [Finset.filter_ne']
      have hsplit := Finset.add_sum_erase Finset.univ (d.qRate i.succ)
        (Finset.mem_univ i.succ)
      rw [d.qRate_row_sum_succ i] at hsplit
      linarith

@[simp]
theorem qMatrix_rate_zero (t : Fin (s + 1)) : d.qMatrix.rate 0 t = 0 := by
  rfl

@[simp]
theorem qMatrix_rate_succ_zero (i : Fin s) :
    d.qMatrix.rate i.succ 0 = (-d.generator).mulVec (fun _ ↦ 1) i := by
  rfl

@[simp]
theorem qMatrix_rate_succ_succ (i j : Fin s) :
    d.qMatrix.rate i.succ j.succ = d.generator i j := by
  rfl

/-- The adjoined state `0` has zero exit rate. -/
@[simp]
theorem qMatrix_exitRate_zero : d.qMatrix.exitRate 0 = 0 := by
  simp [Ripple.CTMC.QMatrix.exitRate]

/-- A transient state's total exit rate is the negative generator diagonal. -/
theorem qMatrix_exitRate_succ (i : Fin s) :
    d.qMatrix.exitRate i.succ = -d.generator i i := by
  have hdiag := d.qMatrix.diag_eq_neg_exitRate i.succ
  rw [qMatrix_rate_succ_succ] at hdiag
  linarith

/-- Every transient state has strictly positive exit rate. -/
theorem qMatrix_exitRate_succ_pos (i : Fin s) :
    0 < d.qMatrix.exitRate i.succ := by
  rw [d.qMatrix_exitRate_succ i]
  exact neg_pos.mpr (d.generator_diag_neg i)

/-- The adjoined state `0` is absorbing. -/
theorem qMatrix_isAbsorbing_zero : d.qMatrix.IsAbsorbing 0 := by
  exact d.qMatrix_exitRate_zero

/-- No transient state is absorbing. -/
theorem qMatrix_not_isAbsorbing_succ (i : Fin s) :
    ¬d.qMatrix.IsAbsorbing i.succ :=
  ne_of_gt (d.qMatrix_exitRate_succ_pos i)

/-- The embedded jump chain stays at the absorbing state. -/
theorem embeddedDTMC_step_zero (t : Fin (s + 1)) :
    d.qMatrix.embeddedDTMC.step 0 t = if t = 0 then 1 else 0 := by
  exact d.qMatrix.embeddedDTMC_step_of_absorbing d.qMatrix_isAbsorbing_zero t

/-- The embedded probability of absorption is its rate divided by the exit rate. -/
theorem embeddedDTMC_step_succ_zero (i : Fin s) :
    d.qMatrix.embeddedDTMC.step i.succ 0 =
      ENNReal.ofReal
        (((-d.generator).mulVec (fun _ ↦ 1) i) / (-d.generator i i)) := by
  rw [d.qMatrix.embeddedDTMC_step_of_nonabsorbing
    (d.qMatrix_not_isAbsorbing_succ i) 0]
  simp [Ripple.CTMC.QMatrix.jumpProb, d.qMatrix_exitRate_succ i]

/-- An off-diagonal embedded probability is its generator rate divided by the exit rate. -/
theorem embeddedDTMC_step_succ_succ {i j : Fin s} (hij : i ≠ j) :
    d.qMatrix.embeddedDTMC.step i.succ j.succ =
      ENNReal.ofReal (d.generator i j / (-d.generator i i)) := by
  rw [d.qMatrix.embeddedDTMC_step_of_nonabsorbing
    (d.qMatrix_not_isAbsorbing_succ i) j.succ]
  simp [Ripple.CTMC.QMatrix.jumpProb, hij, d.qMatrix_exitRate_succ i]

/-- Initial masses on the absorbing and transient CTMC states. -/
noncomputable def initialWeight : Fin (s + 1) → ℝ≥0∞ :=
  Fin.cases (ENNReal.ofReal (1 - d.mass)) fun i ↦ ENNReal.ofReal (d.initial i)

private theorem initialWeight_sum : ∑ x, d.initialWeight x = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [initialWeight, Fin.cases_zero, Fin.cases_succ]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ d.initial_nonneg i)]
  change ENNReal.ofReal (1 - d.mass) + ENNReal.ofReal d.mass = 1
  have hmass_nonneg : 0 ≤ d.mass :=
    Finset.sum_nonneg fun i _ ↦ d.initial_nonneg i
  have hmass_le : d.mass ≤ 1 := by
    simpa [mass] using d.initial_mass_le
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hmass_le) hmass_nonneg]
  simp

/-- The initial probability mass function on the CTMC state space. -/
noncomputable def initialPMF : PMF (Fin (s + 1)) :=
  PMF.ofFintype d.initialWeight d.initialWeight_sum

@[simp]
theorem initialPMF_zero : d.initialPMF 0 = ENNReal.ofReal (1 - d.mass) := by
  simp [initialPMF, initialWeight]

@[simp]
theorem initialPMF_succ (i : Fin s) :
    d.initialPMF i.succ = ENNReal.ofReal (d.initial i) := by
  simp [initialPMF, initialWeight]

/-- The measure-valued form of the initial CTMC distribution. -/
noncomputable def initialMeasure : Measure (Fin (s + 1)) :=
  d.initialPMF.toMeasure

instance : IsProbabilityMeasure d.initialMeasure := by
  unfold initialMeasure
  infer_instance

@[simp]
theorem initialMeasure_singleton_zero :
    d.initialMeasure {0} = ENNReal.ofReal (1 - d.mass) := by
  rw [initialMeasure,
    PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
  exact d.initialPMF_zero

@[simp]
theorem initialMeasure_singleton_succ (i : Fin s) :
    d.initialMeasure {i.succ} = ENNReal.ofReal (d.initial i) := by
  rw [initialMeasure,
    PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
  exact d.initialPMF_succ i

end SSPRK.PhaseTypeData
