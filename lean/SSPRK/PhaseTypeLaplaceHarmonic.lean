import SSPRK.PhaseTypeHoldingLaplace
import SSPRK.PhaseTypeTimeChange
import SSPRK.PhaseTypeLaplace
import SSPRK.PhaseTypeResolvent

/-!
# Laplace harmonic functions for phase-type jump-hold records

The fixed-state phase-type Laplace transforms, extended by one at the absorbing state,
satisfy the actual jump-hold one-step harmonic equation.
-/

open MeasureTheory
open scoped BigOperators

namespace SSPRK.PhaseTypeData

variable {s : ℕ} (d : PhaseTypeData s)

/-- The phase-type Laplace transform extended to the absorbing state. -/
noncomputable def laplaceHarmonic (u : ℝ) : Fin (s + 1) → ℝ :=
  Fin.cases 1 (fun i ↦ ∫ t, Real.exp (-u * t) ∂(d.startAt i).measure)

@[simp]
theorem laplaceHarmonic_zero (u : ℝ) : d.laplaceHarmonic u 0 = 1 := rfl

@[simp]
theorem laplaceHarmonic_succ (u : ℝ) (i : Fin s) :
    d.laplaceHarmonic u i.succ = ∫ t, Real.exp (-u * t) ∂(d.startAt i).measure := rfl

/-- The transient Laplace vector is the generator resolvent applied to the absorption rates. -/
theorem laplaceHarmonic_succ_eq_resolvent (u : ℝ) (hu : 0 ≤ u) (i : Fin s) :
    d.laplaceHarmonic u i.succ =
      ((u • (1 : Matrix (Fin s) (Fin s) ℝ) - d.generator)⁻¹).mulVec
        ((-d.generator).mulVec (fun _ ↦ 1)) i := by
  rw [laplaceHarmonic_succ, (d.startAt i).integral_exp_neg_mul_measure u hu,
    ← (d.startAt i).laplace_resolvent_exit u hu, d.startAt_mass, sub_self, zero_add]
  exact d.startAt_dotProduct i _

theorem laplaceHarmonic_nonneg (u : ℝ) (x : Fin (s + 1)) :
    0 ≤ d.laplaceHarmonic u x := by
  refine Fin.cases (by simp) (fun i ↦ ?_) x
  exact integral_nonneg fun t ↦ (Real.exp_pos _).le

theorem laplaceHarmonic_le_one (u : ℝ) (hu : 0 ≤ u) (x : Fin (s + 1)) :
    d.laplaceHarmonic u x ≤ 1 := by
  refine Fin.cases (by simp) (fun i ↦ ?_) x
  rw [laplaceHarmonic_succ]
  have h := integral_mono_ae ((d.startAt i).integrable_exp_neg_mul_measure u hu)
    (integrable_const (1 : ℝ)) ((d.startAt i).ae_nonneg_measure.mono fun t ht ↦
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) ht))
  simpa using h

/-- The transient Laplace vector solves the generator resolvent equation. -/
theorem laplaceHarmonic_generator_equation (u : ℝ) (hu : 0 ≤ u) (i : Fin s) :
    u * d.laplaceHarmonic u i.succ -
        ∑ j, d.generator i j * d.laplaceHarmonic u j.succ =
      (-d.generator).mulVec (fun _ ↦ 1) i := by
  have hf : (fun j ↦ d.laplaceHarmonic u j.succ) =
      ((u • (1 : Matrix (Fin s) (Fin s) ℝ) - d.generator)⁻¹).mulVec
        ((-d.generator).mulVec (fun _ ↦ 1)) :=
    funext (d.laplaceHarmonic_succ_eq_resolvent u hu)
  have hv : (u • (1 : Matrix (Fin s) (Fin s) ℝ) - d.generator).mulVec
      (fun j ↦ d.laplaceHarmonic u j.succ) = (-d.generator).mulVec (fun _ ↦ 1) := by
    rw [hf, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (d.laplace_shift_det_ne_zero u hu)),
      Matrix.one_mulVec]
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hv
  exact congrFun hv i

/-- The Laplace harmonic observable is integrable for every total jump-hold step. -/
theorem integrable_laplaceHarmonic_jumpHoldStepMeasureTotal
    (u : ℝ) (hu : 0 ≤ u) (x : Fin (s + 1)) :
    Integrable
      (fun record : ℝ × Fin (s + 1) ↦ Real.exp (-u * record.1) *
        d.laplaceHarmonic u record.2) (d.qMatrix.jumpHoldStepMeasureTotal x) := by
  refine Fin.cases ?_ (fun i ↦ ?_) x
  · exact d.integrable_exp_neg_mul_stateFun_jumpHoldStepMeasureTotal_zero u _
  · rw [d.qMatrix.jumpHoldStepMeasureTotal_of_nonabsorbing
      (d.qMatrix_not_isAbsorbing_succ i)]
    exact d.integrable_exp_neg_mul_stateFun_jumpHoldStepMeasure_succ i hu _

/-- The fixed-state phase-type Laplace transforms are harmonic for actual jump-hold records. -/
theorem integral_laplaceHarmonic_jumpHoldStepMeasureTotal
    (u : ℝ) (hu : 0 ≤ u) (x : Fin (s + 1)) :
    (∫ record : ℝ × Fin (s + 1), Real.exp (-u * record.1) *
        d.laplaceHarmonic u record.2 ∂d.qMatrix.jumpHoldStepMeasureTotal x) =
      d.laplaceHarmonic u x := by
  refine Fin.cases ?_ (fun i ↦ ?_) x
  · exact d.integral_exp_neg_mul_stateFun_jumpHoldStepMeasureTotal_zero u _
  · rw [d.qMatrix.jumpHoldStepMeasureTotal_of_nonabsorbing
      (d.qMatrix_not_isAbsorbing_succ i),
      d.integral_exp_neg_mul_stateFun_jumpHoldStepMeasure_succ i hu,
      d.laplaceHarmonic_zero, mul_one]
    have heq := d.laplaceHarmonic_generator_equation u hu i
    have hsum := Finset.sum_filter_add_sum_filter_not Finset.univ (fun j ↦ j ≠ i)
      (fun j ↦ d.generator i j * d.laplaceHarmonic u j.succ)
    simp only [not_not, Finset.filter_eq', Finset.mem_univ, if_true,
      Finset.sum_singleton] at hsum
    have hden : u - d.generator i i ≠ 0 := ne_of_gt
      (sub_pos.mpr ((d.generator_diag_neg i).trans_le hu))
    apply (div_eq_iff hden).mpr
    nlinarith

end SSPRK.PhaseTypeData
