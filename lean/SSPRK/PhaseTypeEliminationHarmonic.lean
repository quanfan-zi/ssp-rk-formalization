import SSPRK.PhaseTypeLaplaceHarmonic

/-!
# Harmonic certificate for deleting the first transient occupation

The first transient state has zero holding-time cost. The remaining states have cost `u`.
The eliminated phase-type Laplace transforms give a bounded harmonic certificate.
-/

open MeasureTheory
open scoped BigOperators

namespace SSPRK.PhaseTypeData

/-- A phase-type Laplace transform is the initial mixture of fixed-state transforms. -/
lemma laplace_eq_initial_harmonic {s : ℕ} (d : PhaseTypeData s)
    (u : ℝ) (hu : 0 ≤ u) :
    (∫ t, Real.exp (-u * t) ∂d.measure) =
      1 - d.mass + ∑ j, d.initial j * d.laplaceHarmonic u j.succ := by
  rw [d.integral_exp_neg_mul_measure u hu, ← d.laplace_resolvent_exit u hu]
  simp only [d.laplaceHarmonic_succ_eq_resolvent u hu, dotProduct]

/-- The generator equation expressed as a discrete transition deficit. -/
lemma laplaceHarmonic_transition_equation {s : ℕ} (d : PhaseTypeData s)
    (u : ℝ) (hu : 0 ≤ u) (i : Fin s) :
    u * d.laplaceHarmonic u i.succ = d.rate *
      ((∑ j, d.transition i j * (d.laplaceHarmonic u j.succ - 1)) -
        (d.laplaceHarmonic u i.succ - 1)) := by
  have h := d.laplaceHarmonic_generator_equation u hu i
  simp only [Matrix.mulVec, dotProduct, mul_one, Matrix.neg_apply, Finset.sum_neg_distrib] at h
  have hs : (∑ j, d.generator i j * (d.laplaceHarmonic u j.succ - 1)) =
      d.rate * ((∑ j, d.transition i j * (d.laplaceHarmonic u j.succ - 1)) -
        (d.laplaceHarmonic u i.succ - 1)) := by
    change d.generator.mulVec (fun j ↦ d.laplaceHarmonic u j.succ - 1) i = _
    rw [generator, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    rfl
  rw [← hs]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  linarith

/-- A transition reward equation gives a one-step jump-hold harmonic identity. -/
lemma integral_jumpHold_eq_of_transition_reward {s : ℕ} (d : PhaseTypeData s)
    (f : Fin (s + 1) → ℝ) (hf0 : f 0 = 1) (i : Fin s)
    (c : ℝ) (hc : 0 ≤ c)
    (heq : c * f i.succ = d.rate *
      ((∑ j, d.transition i j * (f j.succ - 1)) - (f i.succ - 1))) :
    (∫ record : ℝ × Fin (s + 1), Real.exp (-c * record.1) * f record.2
      ∂d.qMatrix.jumpHoldStepMeasureTotal i.succ) = f i.succ := by
  have hgen : (∑ j, d.generator i j * (f j.succ - 1)) =
      d.rate * ((∑ j, d.transition i j * (f j.succ - 1)) - (f i.succ - 1)) := by
    change d.generator.mulVec (fun j ↦ f j.succ - 1) i = _
    rw [generator, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    rfl
  rw [← hgen] at heq
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib] at heq
  rw [d.qMatrix.jumpHoldStepMeasureTotal_of_nonabsorbing
    (d.qMatrix_not_isAbsorbing_succ i),
    d.integral_exp_neg_mul_stateFun_jumpHoldStepMeasure_succ i hc, hf0, mul_one]
  have hsum := Finset.sum_filter_add_sum_filter_not Finset.univ (fun j ↦ j ≠ i)
    (fun j ↦ d.generator i j * f j.succ)
  simp only [not_not, Finset.filter_eq', Finset.mem_univ, if_true,
    Finset.sum_singleton] at hsum
  have hden : c - d.generator i i ≠ 0 := ne_of_gt
    (sub_pos.mpr ((d.generator_diag_neg i).trans_le hc))
  apply (div_eq_iff hden).mpr
  simp only [Matrix.mulVec, dotProduct, Matrix.neg_apply, mul_one, Finset.sum_neg_distrib]
  nlinarith

variable {n : ℕ} (d : PhaseTypeData (n + 1))

/-- The bounded Laplace certificate for the deleted-state reward. -/
noncomputable def eliminationHarmonic (u : ℝ) : Fin (n + 2) → ℝ :=
  Fin.cases 1 (Fin.cases (∫ t, Real.exp (-u * t) ∂d.eliminateZero.measure)
    (fun j ↦ d.eliminateZero.laplaceHarmonic u j.succ))

/-- The pivot state's holding time is omitted from the reward. -/
def eliminationCost (_d : PhaseTypeData (n + 1)) (u : ℝ) (x : Fin (n + 2)) : ℝ :=
  if x = 1 then 0 else u

@[simp] theorem eliminationHarmonic_zero (u : ℝ) : d.eliminationHarmonic u 0 = 1 := rfl

@[simp] theorem eliminationHarmonic_one (u : ℝ) :
    d.eliminationHarmonic u 1 = ∫ t, Real.exp (-u * t) ∂d.eliminateZero.measure := rfl

@[simp] theorem eliminationHarmonic_succ_succ (u : ℝ) (j : Fin n) :
    d.eliminationHarmonic u j.succ.succ = d.eliminateZero.laplaceHarmonic u j.succ := rfl

theorem eliminationHarmonic_nonneg (u : ℝ) (x : Fin (n + 2)) :
    0 ≤ d.eliminationHarmonic u x := by
  refine Fin.cases (by simp) (fun i ↦ ?_) x
  refine Fin.cases ?_ (fun j ↦ d.eliminateZero.laplaceHarmonic_nonneg u j.succ) i
  exact integral_nonneg fun t ↦ (Real.exp_pos _).le

theorem eliminationHarmonic_le_one (u : ℝ) (hu : 0 ≤ u) (x : Fin (n + 2)) :
    d.eliminationHarmonic u x ≤ 1 := by
  refine Fin.cases (by simp) (fun i ↦ ?_) x
  refine Fin.cases ?_ (fun j ↦ d.eliminateZero.laplaceHarmonic_le_one u hu j.succ) i
  have h := integral_mono_ae (d.eliminateZero.integrable_exp_neg_mul_measure u hu)
    (integrable_const (1 : ℝ)) (d.eliminateZero.ae_nonneg_measure.mono fun t ht ↦
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) ht))
  simpa using h

/-- The pivot value is the mixture prescribed by the elimination initial row. -/
lemma eliminationHarmonic_pivot_deficit (u : ℝ) (hu : 0 ≤ u) :
    d.eliminationHarmonic u 1 - 1 =
      ∑ j, d.eliminateZero.initial j * (d.eliminateZero.laplaceHarmonic u j.succ - 1) := by
  rw [d.eliminationHarmonic_one, d.eliminateZero.laplace_eq_initial_harmonic u hu]
  simp only [mass, mul_sub, mul_one, Finset.sum_sub_distrib]
  ring

/-- The deleted-state certificate satisfies the discrete transition reward equation. -/
theorem eliminationHarmonic_transition_equation (u : ℝ) (hu : 0 ≤ u)
    (i : Fin (n + 1)) :
    d.eliminationCost u i.succ * d.eliminationHarmonic u i.succ = d.rate *
      ((∑ j, d.transition i j * (d.eliminationHarmonic u j.succ - 1)) -
        (d.eliminationHarmonic u i.succ - 1)) := by
  have hp := d.eliminationHarmonic_pivot_deficit u hu
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · have hs : (∑ j : Fin n, d.transition 0 j.succ *
        (d.eliminateZero.laplaceHarmonic u j.succ - 1)) =
        d.eliminationPivot * (d.eliminationHarmonic u 1 - 1) := by
      rw [hp, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      change _ = d.eliminationPivot *
        (d.transition 0 j.succ / d.eliminationPivot * _)
      field_simp [d.eliminationPivot_pos.ne']
    rw [Fin.sum_univ_succ]
    simp only [Fin.succ_zero_eq_one, eliminationCost, if_true, zero_mul,
      eliminationHarmonic_succ_succ]
    rw [hs]
    unfold eliminationPivot
    ring
  · have he := d.eliminateZero.laplaceHarmonic_transition_equation u hu i
    have hs : (∑ j, d.eliminateZero.transition i j *
        (d.eliminateZero.laplaceHarmonic u j.succ - 1)) =
        (∑ j : Fin n, d.transition i.succ j.succ *
          (d.eliminateZero.laplaceHarmonic u j.succ - 1)) +
          d.transition i.succ 0 * (d.eliminationHarmonic u 1 - 1) := by
      rw [hp, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp only [eliminateZero_transition, eliminateZero_initial]
      ring
    rw [hs, d.eliminateZero_rate] at he
    rw [Fin.sum_univ_succ]
    have hi : i.succ.succ ≠ (1 : Fin (n + 2)) := by
      intro hi
      have hv := congrArg Fin.val hi
      simp only [Fin.val_succ, Fin.val_one] at hv
      omega
    simp only [eliminationCost, if_neg hi, Fin.succ_zero_eq_one,
      eliminationHarmonic_succ_succ]
    convert he using 1
    ring

theorem eliminationCost_nonneg (u : ℝ) (hu : 0 ≤ u) (x : Fin (n + 2)) :
    0 ≤ d.eliminationCost u x := by
  unfold eliminationCost
  split_ifs <;> positivity

/-- Integrability of the deleted-occupation harmonic observable for the actual step measure. -/
theorem integrable_eliminationHarmonic_jumpHoldStepMeasureTotal
    (u : ℝ) (hu : 0 ≤ u) (x : Fin (n + 2)) :
    Integrable (fun record : ℝ × Fin (n + 2) ↦
      Real.exp (-(d.eliminationCost u x) * record.1) * d.eliminationHarmonic u record.2)
      (d.qMatrix.jumpHoldStepMeasureTotal x) := by
  refine Fin.cases ?_ (fun i ↦ ?_) x
  · exact d.integrable_exp_neg_mul_stateFun_jumpHoldStepMeasureTotal_zero _ _
  · rw [d.qMatrix.jumpHoldStepMeasureTotal_of_nonabsorbing
      (d.qMatrix_not_isAbsorbing_succ i)]
    exact d.integrable_exp_neg_mul_stateFun_jumpHoldStepMeasure_succ i
      (d.eliminationCost_nonneg u hu i.succ) _

/-- The eliminated law supplies a harmonic certificate for deleting pivot holding times. -/
theorem integral_eliminationHarmonic_jumpHoldStepMeasureTotal
    (u : ℝ) (hu : 0 ≤ u) (x : Fin (n + 2)) :
    (∫ record : ℝ × Fin (n + 2),
      Real.exp (-(d.eliminationCost u x) * record.1) * d.eliminationHarmonic u record.2
      ∂d.qMatrix.jumpHoldStepMeasureTotal x) = d.eliminationHarmonic u x := by
  refine Fin.cases ?_ (fun i ↦ ?_) x
  · exact d.integral_exp_neg_mul_stateFun_jumpHoldStepMeasureTotal_zero _ _
  · exact d.integral_jumpHold_eq_of_transition_reward (d.eliminationHarmonic u)
      (d.eliminationHarmonic_zero u) i (d.eliminationCost u i.succ)
      (d.eliminationCost_nonneg u hu i.succ) (d.eliminationHarmonic_transition_equation u hu i)

end SSPRK.PhaseTypeData
