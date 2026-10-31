import SSPRK.ThirdMomentDefect
import SSPRK.PhaseTypeThirdMomentIntegral
import SSPRK.PhaseMomentBound

/-!
# The V2.10 third-moment proof by the exact defect

The state-count induction reuses the established Schur-complement representation and
Green block identities. Its scalar step is the paper's exact remainder and six-square
certificate, not the independent-replacement or length-bias comparison. The smaller
model's variance bound is supplied by the separate minimum-variance theorem.
-/

open MeasureTheory
open scoped BigOperators

namespace SSPRK.PhaseTypeData

/-- The separate variance theorem in the Green-moment normalization. -/
theorem green_second_bound {s : ℕ} (d : PhaseTypeData s) (hs : 0 < s) :
    ((s : ℝ) + 1) * dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)) ^ 2 ≤
      (s : ℝ) * (2 * dotProduct d.initial ((d.green ^ 2).mulVec (fun _ ↦ 1))) := by
  have hleft : (1 - d.transition) * d.green = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr d.transient)
  have hright : d.green * (1 - d.transition) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr d.transient)
  have hbound := phase_second_moment_bound s hs d.transition d.green d.initial
    d.substochastic (d.substochastic.inv_nonneg d.transient) hleft hright
    d.initial_nonneg d.initial_mass_le
  rw [Matrix.mulVec_mulVec, ← pow_two] at hbound
  nlinarith only [hbound]

/-- The normalized block induction step uses exactly the V2.10 defect certificate. -/
theorem phaseBlock_momentClass_of_tail_defect {n : ℕ}
    (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hG : G 0 0 = 1)
    (hη1 : 0 ≤ phaseBlockEta1 G) (hη2 : 0 ≤ phaseBlockEta2 G)
    (hclass : MomentClass n (phaseBlockZ1 G) (phaseBlockZ2 G) (phaseBlockZ3 G)) :
    MomentClass (n + 1 : ℕ) (phaseBlockMoment G 1)
      (phaseBlockMoment G 2) (phaseBlockMoment G 3) := by
  rw [phaseBlock_first_moment G hG, phaseBlock_second_moment G hG,
    phaseBlock_third_moment G hG]
  convert hclass.block_defect hη1 hη2 using 1 <;> push_cast <;> ring

/-- Eliminate the fixed initial state and invoke the smaller phase-count hypothesis. -/
theorem green_zero_momentClass_of_induction_defect {n : ℕ} (d : PhaseTypeData (n + 1))
    (ih : ∀ e : PhaseTypeData n,
      0 < dotProduct e.initial (e.green.mulVec (fun _ ↦ 1)) →
      MomentClass n (dotProduct e.initial (e.green.mulVec (fun _ ↦ 1)))
        (2 * dotProduct e.initial ((e.green ^ 2).mulVec (fun _ ↦ 1)))
        (6 * dotProduct e.initial ((e.green ^ 3).mulVec (fun _ ↦ 1)))) :
    MomentClass (n + 1 : ℕ) (d.green.mulVec (fun _ ↦ 1) 0)
      (2 * (d.green ^ 2).mulVec (fun _ ↦ 1) 0)
      (6 * (d.green ^ 3).mulVec (fun _ ↦ 1) 0) := by
  apply d.green_row_momentClass_of_normalized
  have hz : 0 ≤ phaseBlockZ1 d.normalizedGreen := by
    simpa only [phaseBlockZ1, dotProduct, mul_one] using
      Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) ↦ d.normalizedGreen_nonneg 0 j.succ)
  obtain hzero | hpos := hz.eq_or_lt
  · exact phaseBlock_momentClass_of_upper_zero _ d.normalizedGreen_zero_zero
      (d.normalizedGreen_blockU_eq_zero hzero.symm)
  · have hmean : 0 < dotProduct d.eliminateZero.initial
        (d.eliminateZero.green.mulVec (fun _ ↦ 1)) := by
      rw [d.normalizedGreen_z1] at hpos
      exact (mul_pos_iff_of_pos_left (inv_pos.mpr d.green_pivot_pos)).mp hpos
    have htail := ih d.eliminateZero hmean
    have hn : 0 < n := Nat.cast_pos.mp htail.parameter_pos
    have htail' : MomentClass n
        (dotProduct d.eliminateZero.initial (d.eliminateZero.green.mulVec (fun _ ↦ 1)))
        (2 * dotProduct d.eliminateZero.initial ((d.eliminateZero.green ^ 2).mulVec (fun _ ↦ 1)))
        (6 * dotProduct d.eliminateZero.initial ((d.eliminateZero.green ^ 3).mulVec (fun _ ↦ 1))) :=
      { htail with second_bound := d.eliminateZero.green_second_bound hn }
    apply phaseBlock_momentClass_of_tail_defect _ d.normalizedGreen_zero_zero
      d.normalizedGreen_eta1_nonneg
      (d.normalizedGreen_eta2_nonneg d.normalizedGreen_blockH_nonneg)
    rw [d.normalizedGreen_z1, d.normalizedGreen_z2, d.normalizedGreen_z3]
    exact htail'.scale (inv_pos.mpr d.green_pivot_pos)

/-- V2.10's state-count induction, followed by the finite-mixture Cauchy--Schwarz step. -/
theorem green_moment_class_defect (s : ℕ) (d : PhaseTypeData s)
    (hmean : 0 < dotProduct d.initial (d.green.mulVec (fun _ ↦ 1))) :
    MomentClass s (dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)))
      (2 * dotProduct d.initial ((d.green ^ 2).mulVec (fun _ ↦ 1)))
      (6 * dotProduct d.initial ((d.green ^ 3).mulVec (fun _ ↦ 1))) := by
  induction s with
  | zero =>
    simp only [dotProduct, Finset.univ_eq_empty, Finset.sum_empty, lt_self_iff_false] at hmean
  | succ n ih =>
    apply d.green_moment_class_of_rows _ hmean
    intro i
    let e : Fin (n + 1) ≃ Fin (n + 1) := Equiv.swap 0 i
    have hzero := (d.reindex e).green_zero_momentClass_of_induction_defect ih
    have hrow (k : ℕ) := d.green_pow_mulVec_one_reindex e k 0
    have he : e 0 = i := Equiv.swap_apply_left 0 i
    simp only [he] at hrow
    have hfirst := hrow 1
    simp only [pow_one] at hfirst
    rw [hfirst, hrow 2, hrow 3] at hzero
    exact hzero

/-- Transfer the new defect proof to actual integral moments. -/
theorem integral_moment_class_defect {s : ℕ} (d : PhaseTypeData s)
    (hmean : 0 < ∫ x, x ∂d.measure) :
    MomentClass s (∫ x, x ∂d.measure) (∫ x, x ^ 2 ∂d.measure) (∫ x, x ^ 3 ∂d.measure) := by
  apply d.integral_momentClass_of_green
  apply green_moment_class_defect s d
  rw [d.integral_id_measure] at hmean
  exact (div_pos_iff_of_pos_right d.rate_pos).mp hmean

/-- The third-moment inequality proved through the V2.10 remainder. -/
theorem third_moment_lower_bound_defect {s : ℕ} (d : PhaseTypeData s)
    (hmean : 0 < ∫ x, x ∂d.measure) :
    ((s : ℝ) + 2) * (∫ x, x ^ 2 ∂d.measure) ^ 2 ≤
      ((s : ℝ) + 1) * (∫ x, x ∂d.measure) * (∫ x, x ^ 3 ∂d.measure) :=
  (d.integral_moment_class_defect hmean).third_bound

/-- The paper's adjacent moment ratio, now supplied by the defect proof. -/
theorem third_moment_ratio_lower_bound_defect {s : ℕ} (d : PhaseTypeData s)
    (hmean : 0 < ∫ x, x ∂d.measure) :
    ((s : ℝ) + 2) / ((s : ℝ) + 1) ≤
      (∫ x, x ∂d.measure) * (∫ x, x ^ 3 ∂d.measure) / (∫ x, x ^ 2 ∂d.measure) ^ 2 := by
  have hc := d.integral_moment_class_defect hmean
  apply (div_le_div_iff₀ (by positivity : 0 < (s : ℝ) + 1)
    (sq_pos_of_pos hc.second_pos)).mpr
  nlinarith only [hc.third_bound]

end SSPRK.PhaseTypeData
