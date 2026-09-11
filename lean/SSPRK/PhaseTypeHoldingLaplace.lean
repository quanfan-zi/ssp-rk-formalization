import SSPRK.ErlangLaplace
import SSPRK.PhaseTypeQMatrix

/-!
# One-step Laplace transforms for phase-type holding times

This file factors a jump-hold Laplace integral into its holding-time and embedded-chain
parts, then expands the result for the Q-matrix associated with phase-type data.
-/

open MeasureTheory
open scoped BigOperators

namespace SSPRK

/-- The nonnegative Laplace kernel is integrable under every nonabsorbing holding-time law. -/
theorem integrable_exp_neg_mul_holdingTimeMeasure
    {S : Type*} [Fintype S] [DecidableEq S]
    (Q : Ripple.CTMC.QMatrix S) {x : S} (h : ¬Q.IsAbsorbing x)
    {u : ℝ} (hu : 0 ≤ u) :
    Integrable (fun t : ℝ ↦ Real.exp (-u * t)) (Q.holdingTimeMeasure h) := by
  letI := Q.isProbabilityMeasure_holdingTimeMeasure h
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards [Q.holdingTimeMeasure_pos_ae h] with t ht
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) ht.le)

/-- Every real-valued function on a finite state space is integrable under an embedded row. -/
theorem integrable_stateFun_embeddedStepMeasure
    {S : Type*} [Fintype S] [DecidableEq S] [Countable S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (Q : Ripple.CTMC.QMatrix S) (x : S) (f : S → ℝ) :
    Integrable f (Q.embeddedStepMeasure x) := by
  letI := Q.isProbabilityMeasure_embeddedStepMeasure x
  let c : ℝ := ∑ y, ‖f y‖
  have hc : ∀ y : S, ‖f y‖ ≤ c := by
    intro y
    exact Finset.single_le_sum (fun z _ ↦ norm_nonneg (f z)) (Finset.mem_univ y)
  have hc_nonneg : 0 ≤ c := Finset.sum_nonneg fun y _ ↦ norm_nonneg (f y)
  refine (integrable_const c).mono'
    (Measurable.of_discrete (f := f)).aestronglyMeasurable ?_
  filter_upwards with y
  simpa [Real.norm_eq_abs, abs_of_nonneg hc_nonneg] using hc y

/-- The product of a nonnegative Laplace kernel and a finite-state observable is integrable. -/
theorem integrable_exp_neg_mul_stateFun_jumpHoldStepMeasure
    {S : Type*} [Fintype S] [DecidableEq S] [Countable S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (Q : Ripple.CTMC.QMatrix S) {x : S} (h : ¬Q.IsAbsorbing x)
    {u : ℝ} (hu : 0 ≤ u) (f : S → ℝ) :
    Integrable (fun record : ℝ × S ↦ Real.exp (-u * record.1) * f record.2)
      (Q.jumpHoldStepMeasure h) := by
  unfold Ripple.CTMC.QMatrix.jumpHoldStepMeasure
  exact (integrable_exp_neg_mul_holdingTimeMeasure Q h hu).mul_prod
    (integrable_stateFun_embeddedStepMeasure Q x f)

/-- A one-step jump-hold Laplace integral factors into holding and embedded-chain terms. -/
theorem integral_exp_neg_mul_stateFun_jumpHoldStepMeasure
    {S : Type*} [Fintype S] [DecidableEq S] [Countable S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (Q : Ripple.CTMC.QMatrix S) {x : S} (h : ¬Q.IsAbsorbing x)
    {u : ℝ} (hu : 0 ≤ u) (f : S → ℝ) :
    (∫ record : ℝ × S, Real.exp (-u * record.1) * f record.2
      ∂Q.jumpHoldStepMeasure h) =
      Q.exitRate x / (Q.exitRate x + u) *
        ∫ y, f y ∂Q.embeddedStepMeasure x := by
  unfold Ripple.CTMC.QMatrix.jumpHoldStepMeasure
  letI := Q.isProbabilityMeasure_holdingTimeMeasure h
  letI := Q.isProbabilityMeasure_embeddedStepMeasure x
  calc
    (∫ record : ℝ × S, Real.exp (-u * record.1) * f record.2
        ∂(Q.holdingTimeMeasure h).prod (Q.embeddedStepMeasure x)) =
        (∫ t : ℝ, Real.exp (-u * t) ∂Q.holdingTimeMeasure h) *
          ∫ y, f y ∂Q.embeddedStepMeasure x :=
      integral_prod_mul (fun t : ℝ ↦ Real.exp (-u * t)) f
    _ = Q.exitRate x / (Q.exitRate x + u) *
          ∫ y, f y ∂Q.embeddedStepMeasure x := by
      congr 1
      simpa [Ripple.CTMC.QMatrix.holdingTimeMeasure, ProbabilityTheory.expMeasure] using
        integral_exp_neg_mul_erlangMeasure 0 (Q.exitRate_pos_of_nonabsorbing h) hu

namespace PhaseTypeData

variable {s : ℕ} (d : PhaseTypeData s)

/-- The phase-type one-step Laplace integrand is integrable from every transient state. -/
theorem integrable_exp_neg_mul_stateFun_jumpHoldStepMeasure_succ
    (i : Fin s) {u : ℝ} (hu : 0 ≤ u) (f : Fin (s + 1) → ℝ) :
    Integrable
      (fun record : ℝ × Fin (s + 1) ↦ Real.exp (-u * record.1) * f record.2)
      (d.qMatrix.jumpHoldStepMeasure (d.qMatrix_not_isAbsorbing_succ i)) :=
  integrable_exp_neg_mul_stateFun_jumpHoldStepMeasure d.qMatrix
    (d.qMatrix_not_isAbsorbing_succ i) hu f

/-- The phase-type one-step Laplace integral expanded in generator entries. -/
theorem integral_exp_neg_mul_stateFun_jumpHoldStepMeasure_succ
    (i : Fin s) {u : ℝ} (hu : 0 ≤ u) (f : Fin (s + 1) → ℝ) :
    (∫ record : ℝ × Fin (s + 1),
        Real.exp (-u * record.1) * f record.2
        ∂d.qMatrix.jumpHoldStepMeasure (d.qMatrix_not_isAbsorbing_succ i)) =
      (((-d.generator).mulVec (fun _ ↦ 1) i) * f 0 +
          ∑ j ∈ Finset.univ.filter (fun j ↦ j ≠ i), d.generator i j * f j.succ) /
        (u - d.generator i i) := by
  rw [SSPRK.integral_exp_neg_mul_stateFun_jumpHoldStepMeasure
    d.qMatrix (d.qMatrix_not_isAbsorbing_succ i) hu f]
  have hsum :=
    d.qMatrix.exitRate_mul_integral_embeddedStepMeasure_eq_sum_rate
      (d.qMatrix_not_isAbsorbing_succ i) f
  rw [Finset.sum_filter, Fin.sum_univ_succ] at hsum
  have hsum' :
      d.qMatrix.exitRate i.succ *
          (∫ y, f y ∂d.qMatrix.embeddedStepMeasure i.succ) =
        (-d.generator).mulVec (fun _ ↦ 1) i * f 0 +
          ∑ j ∈ Finset.univ.filter (fun j ↦ j ≠ i),
            d.generator i j * f j.succ := by
    simpa [Finset.sum_filter] using hsum
  calc
    d.qMatrix.exitRate i.succ / (d.qMatrix.exitRate i.succ + u) *
          (∫ y, f y ∂d.qMatrix.embeddedStepMeasure i.succ) =
        (d.qMatrix.exitRate i.succ *
          (∫ y, f y ∂d.qMatrix.embeddedStepMeasure i.succ)) /
          (d.qMatrix.exitRate i.succ + u) := by ring
    _ = (((-d.generator).mulVec (fun _ ↦ 1) i) * f 0 +
          ∑ j ∈ Finset.univ.filter (fun j ↦ j ≠ i),
            d.generator i j * f j.succ) /
        (d.qMatrix.exitRate i.succ + u) := by rw [hsum']
    _ = (((-d.generator).mulVec (fun _ ↦ 1) i) * f 0 +
          ∑ j ∈ Finset.univ.filter (fun j ↦ j ≠ i),
            d.generator i j * f j.succ) /
        (u - d.generator i i) := by
      rw [d.qMatrix_exitRate_succ i]
      ring

/-- The Laplace integrand is integrable for the absorbing-state terminal marker. -/
theorem integrable_exp_neg_mul_stateFun_jumpHoldStepMeasureTotal_zero
    (u : ℝ) (f : Fin (s + 1) → ℝ) :
    Integrable
      (fun record : ℝ × Fin (s + 1) ↦ Real.exp (-u * record.1) * f record.2)
      (d.qMatrix.jumpHoldStepMeasureTotal 0) := by
  rw [d.qMatrix.jumpHoldStepMeasureTotal_of_absorbing d.qMatrix_isAbsorbing_zero]
  exact integrable_dirac (by finiteness)

/-- At the absorbing state, the total one-step Laplace integral evaluates to `f 0`. -/
@[simp]
theorem integral_exp_neg_mul_stateFun_jumpHoldStepMeasureTotal_zero
    (u : ℝ) (f : Fin (s + 1) → ℝ) :
    (∫ record : ℝ × Fin (s + 1),
        Real.exp (-u * record.1) * f record.2
        ∂d.qMatrix.jumpHoldStepMeasureTotal 0) = f 0 := by
  rw [d.qMatrix.jumpHoldStepMeasureTotal_of_absorbing d.qMatrix_isAbsorbing_zero]
  simp

end PhaseTypeData

end SSPRK
