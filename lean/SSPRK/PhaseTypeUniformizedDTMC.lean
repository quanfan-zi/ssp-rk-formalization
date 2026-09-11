import SSPRK.PhaseTypeQMatrix

/-!
# Uniformized discrete chains for phase-type data

This file constructs the discrete-time chain that records every event of the
uniformizing Poisson clock. Unlike the embedded jump chain of `qMatrix`, this chain
retains transient self-loops. Its transient block is exactly `transition`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace SSPRK.PhaseTypeData

variable {s : ℕ} (d : PhaseTypeData s)

/-- The exit probability and the transient row sum add to one. -/
theorem exit_add_row_sum (i : Fin s) : d.exit i + ∑ j, d.transition i j = 1 := by
  simp [exit, Matrix.mulVec, dotProduct, Matrix.one_apply]

/-- The transition matrix of the uniformized chain, including the absorbing state `0`. -/
noncomputable def uniformizedTransition : Matrix (Fin (s + 1)) (Fin (s + 1)) ℝ :=
  fun x ↦ Fin.cases (fun y ↦ if y = 0 then 1 else 0)
    (fun i ↦ Fin.cases (d.exit i) (fun j ↦ d.transition i j)) x

@[simp]
theorem uniformizedTransition_zero (t : Fin (s + 1)) :
    d.uniformizedTransition 0 t = if t = 0 then 1 else 0 := by
  simp [uniformizedTransition]

@[simp]
theorem uniformizedTransition_succ_zero (i : Fin s) :
    d.uniformizedTransition i.succ 0 = d.exit i := by
  simp [uniformizedTransition]

@[simp]
theorem uniformizedTransition_succ_succ (i j : Fin s) :
    d.uniformizedTransition i.succ j.succ = d.transition i j := by
  simp [uniformizedTransition]

/-- Every entry of the uniformized transition matrix is nonnegative. -/
theorem uniformizedTransition_nonneg (x y : Fin (s + 1)) :
    0 ≤ d.uniformizedTransition x y := by
  induction x using Fin.cases with
  | zero =>
      simp only [uniformizedTransition_zero]
      split_ifs <;> positivity
  | succ i =>
      induction y using Fin.cases with
      | zero => simp [d.exit_nonneg]
      | succ j => simp [d.substochastic.nonneg]

/-- Every row of the uniformized transition matrix sums to one. -/
theorem uniformizedTransition_row_sum (x : Fin (s + 1)) :
    ∑ y, d.uniformizedTransition x y = 1 := by
  induction x using Fin.cases with
  | zero =>
      rw [Fin.sum_univ_succ]
      simp
  | succ i =>
      rw [Fin.sum_univ_succ]
      simp only [uniformizedTransition_succ_zero, uniformizedTransition_succ_succ]
      exact d.exit_add_row_sum i

/-- Powers of the uniformized transition matrix remain entrywise nonnegative. -/
theorem uniformizedTransition_pow_nonneg (n : ℕ) (x y : Fin (s + 1)) :
    0 ≤ (d.uniformizedTransition ^ n) x y := by
  induction n generalizing x y with
  | zero =>
      simp [Matrix.one_apply]
      split_ifs <;> positivity
  | succ n ih =>
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun k _ ↦
        mul_nonneg (ih x k) (d.uniformizedTransition_nonneg k y)

/-- The absorbing row stays the point mass at `0` under every matrix power. -/
@[simp]
theorem uniformizedTransition_pow_zero (n : ℕ) (t : Fin (s + 1)) :
    (d.uniformizedTransition ^ n) 0 t = if t = 0 then 1 else 0 := by
  induction n generalizing t with
  | zero => simp [Matrix.one_apply, eq_comm]
  | succ n ih =>
      rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]
      simp [ih]

/-- The transient block of every power is the corresponding power of `transition`. -/
@[simp]
theorem uniformizedTransition_pow_succ_succ (n : ℕ) (i j : Fin s) :
    (d.uniformizedTransition ^ n) i.succ j.succ = (d.transition ^ n) i j := by
  induction n generalizing i j with
  | zero => simp [Matrix.one_apply]
  | succ n ih =>
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_succ]
      simp [ih]

/-- ENNReal-valued weights of one uniformized transition step. -/
noncomputable def uniformizedStepWeight (x y : Fin (s + 1)) : ℝ≥0∞ :=
  ENNReal.ofReal (d.uniformizedTransition x y)

private theorem uniformizedStepWeight_sum (x : Fin (s + 1)) :
    ∑ y, d.uniformizedStepWeight x y = 1 := by
  simp only [uniformizedStepWeight]
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun y _ ↦ d.uniformizedTransition_nonneg x y)]
  rw [d.uniformizedTransition_row_sum]
  simp

/-- The one-step PMF of the uniformized discrete chain. -/
noncomputable def uniformizedStepPMF (x : Fin (s + 1)) : PMF (Fin (s + 1)) :=
  PMF.ofFintype (d.uniformizedStepWeight x) (d.uniformizedStepWeight_sum x)

@[simp]
theorem uniformizedStepPMF_apply (x y : Fin (s + 1)) :
    d.uniformizedStepPMF x y = ENNReal.ofReal (d.uniformizedTransition x y) := by
  simp [uniformizedStepPMF, uniformizedStepWeight]

/-- The uniformized discrete-time Markov chain. -/
noncomputable def uniformizedDTMC : Ripple.CTMC.DTMC (Fin (s + 1)) where
  step := d.uniformizedStepPMF

@[simp]
theorem uniformizedDTMC_step_apply (x y : Fin (s + 1)) :
    d.uniformizedDTMC.step x y = ENNReal.ofReal (d.uniformizedTransition x y) := by
  exact d.uniformizedStepPMF_apply x y

/-- The measure kernel corresponding to one uniformized step. -/
noncomputable def uniformizedKernel : Kernel (Fin (s + 1)) (Fin (s + 1)) :=
  Kernel.ofFunOfCountable fun x ↦ (d.uniformizedStepPMF x).toMeasure

instance : IsMarkovKernel d.uniformizedKernel where
  isProbabilityMeasure x := by
    change IsProbabilityMeasure ((d.uniformizedStepPMF x).toMeasure)
    infer_instance

@[simp]
theorem uniformizedKernel_apply (x : Fin (s + 1)) :
    d.uniformizedKernel x = (d.uniformizedStepPMF x).toMeasure :=
  rfl

@[simp]
theorem uniformizedKernel_apply_singleton (x y : Fin (s + 1)) :
    d.uniformizedKernel x {y} = ENNReal.ofReal (d.uniformizedTransition x y) := by
  rw [uniformizedKernel_apply,
    PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
  exact d.uniformizedStepPMF_apply x y

/-- DTMC iteration agrees entrywise with powers of the real transition matrix. -/
theorem uniformizedDTMC_stepN_apply (n : ℕ) (x y : Fin (s + 1)) :
    d.uniformizedDTMC.stepN n x y =
      ENNReal.ofReal ((d.uniformizedTransition ^ n) x y) := by
  induction n generalizing x y with
  | zero =>
      simp only [Ripple.CTMC.DTMC.stepN, PMF.pure_apply, pow_zero,
        Matrix.one_apply]
      by_cases hxy : x = y
      · subst y
        simp
      · have hyx : y ≠ x := Ne.symm hxy
        simp [hxy, hyx]
  | succ n ih =>
      rw [Ripple.CTMC.DTMC.stepN, PMF.bind_apply, tsum_fintype]
      simp_rw [ih, d.uniformizedDTMC_step_apply]
      simp_rw [← ENNReal.ofReal_mul (d.uniformizedTransition_pow_nonneg n x _)]
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · rw [pow_succ, Matrix.mul_apply]
      · intro k _
        exact mul_nonneg (d.uniformizedTransition_pow_nonneg n x k)
          (d.uniformizedTransition_nonneg k y)

/-- The n-step transient-to-transient probabilities are powers of `transition`. -/
theorem uniformizedDTMC_stepN_succ_succ (n : ℕ) (i j : Fin s) :
    d.uniformizedDTMC.stepN n i.succ j.succ =
      ENNReal.ofReal ((d.transition ^ n) i j) := by
  rw [d.uniformizedDTMC_stepN_apply]
  simp

/-- The initial PMF of the uniformized chain. -/
noncomputable def uniformizedInitialPMF : PMF (Fin (s + 1)) :=
  d.initialPMF

@[simp]
theorem uniformizedInitialPMF_zero :
    d.uniformizedInitialPMF 0 = ENNReal.ofReal (1 - d.mass) := by
  exact d.initialPMF_zero

@[simp]
theorem uniformizedInitialPMF_succ (i : Fin s) :
    d.uniformizedInitialPMF i.succ = ENNReal.ofReal (d.initial i) := by
  exact d.initialPMF_succ i

/-- The measure-valued initial law of the uniformized chain. -/
noncomputable def uniformizedInitialMeasure : Measure (Fin (s + 1)) :=
  d.uniformizedInitialPMF.toMeasure

instance : IsProbabilityMeasure d.uniformizedInitialMeasure := by
  unfold uniformizedInitialMeasure
  infer_instance

@[simp]
theorem uniformizedInitialMeasure_singleton_zero :
    d.uniformizedInitialMeasure {0} = ENNReal.ofReal (1 - d.mass) := by
  rw [uniformizedInitialMeasure,
    PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
  exact d.uniformizedInitialPMF_zero

@[simp]
theorem uniformizedInitialMeasure_singleton_succ (i : Fin s) :
    d.uniformizedInitialMeasure {i.succ} = ENNReal.ofReal (d.initial i) := by
  rw [uniformizedInitialMeasure,
    PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
  exact d.uniformizedInitialPMF_succ i

/-- The state law after `n` uniformization events, obtained by iterating the DTMC. -/
noncomputable def uniformizedLawN (n : ℕ) : PMF (Fin (s + 1)) :=
  d.uniformizedInitialPMF.bind (d.uniformizedDTMC.stepN n)

/-- The transient point masses after `n` steps are the initial row times `transition ^ n`. -/
theorem uniformizedLawN_succ (n : ℕ) (j : Fin s) :
    d.uniformizedLawN n j.succ =
      ENNReal.ofReal (Matrix.vecMul d.initial (d.transition ^ n) j) := by
  rw [uniformizedLawN, PMF.bind_apply, tsum_fintype, Fin.sum_univ_succ]
  simp only [uniformizedInitialPMF_zero, uniformizedInitialPMF_succ,
    d.uniformizedDTMC_stepN_apply, d.uniformizedTransition_pow_zero,
    d.uniformizedTransition_pow_succ_succ]
  simp only [Fin.succ_ne_zero, if_false, ENNReal.ofReal_zero, mul_zero, zero_add]
  simp_rw [← ENNReal.ofReal_mul (d.initial_nonneg _)]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · rfl
  · intro i _
    exact mul_nonneg (d.initial_nonneg i) ((d.substochastic.pow n).nonneg i j)

/-- Every transient component of the iterated initial row is nonnegative. -/
theorem initial_vecMul_transition_pow_nonneg (n : ℕ) (j : Fin s) :
    0 ≤ Matrix.vecMul d.initial (d.transition ^ n) j := by
  simp only [Matrix.vecMul, dotProduct]
  exact Finset.sum_nonneg fun i _ ↦
    mul_nonneg (d.initial_nonneg i) ((d.substochastic.pow n).nonneg i j)

/-- Total mass in transient states after `n` uniformization events. -/
noncomputable def uniformizedSurvivalMass (n : ℕ) : ℝ≥0∞ :=
  ∑ j : Fin s, d.uniformizedLawN n j.succ

/-- The n-step survival mass is the standard transient matrix-power expression. -/
theorem uniformizedSurvivalMass_eq (n : ℕ) :
    d.uniformizedSurvivalMass n = ENNReal.ofReal
      (dotProduct d.initial ((d.transition ^ n).mulVec (fun _ ↦ 1))) := by
  rw [uniformizedSurvivalMass]
  simp_rw [d.uniformizedLawN_succ]
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun j _ ↦ d.initial_vecMul_transition_pow_nonneg n j)]
  congr 1
  calc
    ∑ j, Matrix.vecMul d.initial (d.transition ^ n) j =
        ∑ j, ∑ i, d.initial i * (d.transition ^ n) i j := rfl
    _ = ∑ i, ∑ j, d.initial i * (d.transition ^ n) i j := Finset.sum_comm
    _ = ∑ i, d.initial i * ∑ j, (d.transition ^ n) i j := by
      simp only [Finset.mul_sum]
    _ = dotProduct d.initial ((d.transition ^ n).mulVec (fun _ ↦ 1)) := by
      simp [dotProduct, Matrix.mulVec]

/-- Probability flow from transient states into `0` at step `n + 1`. -/
noncomputable def uniformizedAbsorptionAtStep (n : ℕ) : ℝ≥0∞ :=
  ∑ i : Fin s, d.uniformizedLawN n i.succ * d.uniformizedDTMC.step i.succ 0

/-- Advancing the iterated initial law by one step is PMF bind with the step kernel. -/
theorem uniformizedLawN_succ_eq_bind (n : ℕ) :
    d.uniformizedLawN (n + 1) =
      (d.uniformizedLawN n).bind d.uniformizedDTMC.step := by
  rw [uniformizedLawN, Ripple.CTMC.DTMC.stepN]
  exact (PMF.bind_bind d.uniformizedInitialPMF
    (d.uniformizedDTMC.stepN n) d.uniformizedDTMC.step).symm

/-- The new mass at `0` in step `n + 1` is exactly the transient-to-zero flow. -/
theorem uniformizedLawN_zero_increment (n : ℕ) :
    d.uniformizedLawN (n + 1) 0 =
      d.uniformizedLawN n 0 + d.uniformizedAbsorptionAtStep n := by
  rw [d.uniformizedLawN_succ_eq_bind n, PMF.bind_apply, tsum_fintype,
    Fin.sum_univ_succ]
  simp [uniformizedAbsorptionAtStep]

/-- First absorption at step `n + 1` has mass `weight n`. -/
theorem uniformizedAbsorptionAtStep_eq_weight (n : ℕ) :
    d.uniformizedAbsorptionAtStep n = ENNReal.ofReal (d.weight n) := by
  rw [uniformizedAbsorptionAtStep]
  simp_rw [d.uniformizedLawN_succ, d.uniformizedDTMC_step_apply,
    d.uniformizedTransition_succ_zero]
  simp_rw [← ENNReal.ofReal_mul (d.initial_vecMul_transition_pow_nonneg n _)]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    calc
      ∑ i, Matrix.vecMul d.initial (d.transition ^ n) i * d.exit i =
          ∑ i, (∑ j, d.initial j * (d.transition ^ n) j i) * d.exit i := rfl
      _ = ∑ i, ∑ j, d.initial j * (d.transition ^ n) j i * d.exit i := by
        simp only [Finset.sum_mul]
      _ = ∑ j, ∑ i, d.initial j * (d.transition ^ n) j i * d.exit i :=
        Finset.sum_comm
      _ = d.weight n := by
        simp [weight, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  · intro i _
    exact mul_nonneg (d.initial_vecMul_transition_pow_nonneg n i) (d.exit_nonneg i)

/-- Mass function of the first absorption step, including immediate absorption at step zero. -/
noncomputable def uniformizedFirstAbsorptionMass : ℕ → ℝ≥0∞
  | 0 => d.uniformizedInitialPMF 0
  | n + 1 => d.uniformizedAbsorptionAtStep n

/-- Step zero carries exactly the immediate-absorption mass. -/
@[simp]
theorem uniformizedFirstAbsorptionMass_zero :
    d.uniformizedFirstAbsorptionMass 0 = ENNReal.ofReal (1 - d.mass) := by
  simp [uniformizedFirstAbsorptionMass]

/-- First absorption at the positive step `n + 1` has mass `weight n`. -/
@[simp]
theorem uniformizedFirstAbsorptionMass_succ (n : ℕ) :
    d.uniformizedFirstAbsorptionMass (n + 1) = ENNReal.ofReal (d.weight n) := by
  exact d.uniformizedAbsorptionAtStep_eq_weight n

/-- Positive-step absorption mass is the increment of mass at the absorbing state. -/
theorem uniformizedLawN_zero_add_firstAbsorptionMass (n : ℕ) :
    d.uniformizedLawN (n + 1) 0 =
      d.uniformizedLawN n 0 + d.uniformizedFirstAbsorptionMass (n + 1) := by
  rw [d.uniformizedLawN_zero_increment]
  rfl

end SSPRK.PhaseTypeData
