import SSPRK.PhaseTypeThirdMoment
import SSPRK.MomentAlgebraEquality

/-! At a fixed initial state, sharpness of the third-moment bound forces the second bound. -/

open scoped BigOperators

namespace SSPRK.PhaseTypeData

theorem normalizedGreen_second_eq_of_third_eq {n : ℕ} (d : PhaseTypeData (n + 1))
    (heq : ((n : ℝ) + 3) * (phaseBlockMoment d.normalizedGreen 2) ^ 2 =
      ((n : ℝ) + 2) * phaseBlockMoment d.normalizedGreen 1 *
        phaseBlockMoment d.normalizedGreen 3) :
    ((n : ℝ) + 2) * (phaseBlockMoment d.normalizedGreen 1) ^ 2 =
      ((n : ℝ) + 1) * phaseBlockMoment d.normalizedGreen 2 := by
  have hz : 0 ≤ phaseBlockZ1 d.normalizedGreen := by
    simpa only [phaseBlockZ1, dotProduct, mul_one] using
      Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) ↦ d.normalizedGreen_nonneg 0 j.succ)
  obtain hzero | hpos := hz.eq_or_lt
  · have hU := d.normalizedGreen_blockU_eq_zero hzero.symm
    simp [phaseBlock_first_moment _ d.normalizedGreen_zero_zero,
      phaseBlock_second_moment _ d.normalizedGreen_zero_zero,
      phaseBlock_third_moment _ d.normalizedGreen_zero_zero,
      phaseBlockZ1, phaseBlockZ2, phaseBlockZ3, phaseBlockEta1, phaseBlockEta2, hU] at heq ⊢
    nlinarith only [heq]
  · have hmean : 0 < dotProduct d.eliminateZero.initial
        (d.eliminateZero.green.mulVec (fun _ ↦ 1)) := by
      rw [d.normalizedGreen_z1] at hpos
      exact (mul_pos_iff_of_pos_left (inv_pos.mpr d.green_pivot_pos)).mp hpos
    have htail : MomentClass n (phaseBlockZ1 d.normalizedGreen)
        (phaseBlockZ2 d.normalizedGreen) (phaseBlockZ3 d.normalizedGreen) := by
      rw [d.normalizedGreen_z1, d.normalizedGreen_z2, d.normalizedGreen_z3]
      exact (green_moment_class n d.eliminateZero hmean).scale (inv_pos.mpr d.green_pivot_pos)
    have haux := auxiliary_moment_class d.normalizedGreen_eta1_nonneg
      (d.normalizedGreen_eta2_nonneg d.normalizedGreen_blockH_nonneg)
    have hsharp := third_moment_add_eq_conditions htail haux (by
      rw [phaseBlock_first_moment _ d.normalizedGreen_zero_zero,
        phaseBlock_second_moment _ d.normalizedGreen_zero_zero,
        phaseBlock_third_moment _ d.normalizedGreen_zero_zero] at heq
      convert heq using 1 <;> ring)
    have hz1 : phaseBlockZ1 d.normalizedGreen = n := by
      have hratio := hsharp.2.2
      simpa only [div_one, div_eq_one_iff_eq htail.parameter_pos.ne'] using hratio
    have hz2 : phaseBlockZ2 d.normalizedGreen = (n : ℝ) * (n + 1) := by
      apply mul_left_cancel₀ htail.parameter_pos.ne'
      have hsecond := hsharp.1
      rw [hz1] at hsecond
      nlinarith only [hsecond]
    have haux2 : 2 * (1 + phaseBlockEta1 d.normalizedGreen) = 2 := by
      nlinarith only [hsharp.2.1]
    rw [phaseBlock_first_moment _ d.normalizedGreen_zero_zero,
      phaseBlock_second_moment _ d.normalizedGreen_zero_zero, haux2, hz1, hz2]
    ring

theorem normalizedGreen_phaseBlockMoment {n : ℕ} (d : PhaseTypeData (n + 1)) (k : ℕ) :
    phaseBlockMoment d.normalizedGreen k = (d.green 0 0)⁻¹ ^ k *
      ((k.factorial : ℝ) * (d.green ^ k).mulVec (fun _ ↦ 1) 0) := by
  rw [phaseBlockMoment, d.normalizedGreen_power_row]
  ring

theorem green_zero_second_eq_of_third_eq {n : ℕ} (d : PhaseTypeData (n + 1))
    (heq : ((n : ℝ) + 3) * (2 * (d.green ^ 2).mulVec (fun _ ↦ 1) 0) ^ 2 =
      ((n : ℝ) + 2) * d.green.mulVec (fun _ ↦ 1) 0 *
        (6 * (d.green ^ 3).mulVec (fun _ ↦ 1) 0)) :
    ((n : ℝ) + 2) * (d.green.mulVec (fun _ ↦ 1) 0) ^ 2 =
      ((n : ℝ) + 1) * (2 * (d.green ^ 2).mulVec (fun _ ↦ 1) 0) := by
  have hfirst : phaseBlockMoment d.normalizedGreen 1 =
      (d.green 0 0)⁻¹ * d.green.mulVec (fun _ ↦ 1) 0 := by
    simpa only [Nat.factorial_one, Nat.cast_one, one_mul, pow_one] using
      d.normalizedGreen_phaseBlockMoment 1
  have hsecond : phaseBlockMoment d.normalizedGreen 2 =
      (d.green 0 0)⁻¹ ^ 2 * (2 * (d.green ^ 2).mulVec (fun _ ↦ 1) 0) := by
    exact d.normalizedGreen_phaseBlockMoment 2
  have hthird : phaseBlockMoment d.normalizedGreen 3 =
      (d.green 0 0)⁻¹ ^ 3 * (6 * (d.green ^ 3).mulVec (fun _ ↦ 1) 0) := by
    exact d.normalizedGreen_phaseBlockMoment 3
  have hnormalized : ((n : ℝ) + 3) * (phaseBlockMoment d.normalizedGreen 2) ^ 2 =
      ((n : ℝ) + 2) * phaseBlockMoment d.normalizedGreen 1 *
        phaseBlockMoment d.normalizedGreen 3 := by
    rw [hfirst, hsecond, hthird]
    nlinarith only [congrArg (fun t : ℝ ↦ (d.green 0 0)⁻¹ ^ 4 * t) heq]
  have hsharp := d.normalizedGreen_second_eq_of_third_eq hnormalized
  rw [hfirst, hsecond] at hsharp
  apply mul_left_cancel₀ (pow_ne_zero 2 (inv_ne_zero d.green_pivot_pos.ne'))
  nlinarith only [hsharp]

/-- At a deterministic initial state, third-moment sharpness implies second-moment sharpness. -/
theorem green_second_eq_of_third_eq {s : ℕ} (d : PhaseTypeData s) (hs : 0 < s) (i : Fin s)
    (heq : ((s : ℝ) + 2) * (2 * (d.green ^ 2).mulVec (fun _ ↦ 1) i) ^ 2 =
      ((s : ℝ) + 1) * d.green.mulVec (fun _ ↦ 1) i *
        (6 * (d.green ^ 3).mulVec (fun _ ↦ 1) i)) :
    ((s : ℝ) + 1) * (d.green.mulVec (fun _ ↦ 1) i) ^ 2 =
      (s : ℝ) * (2 * (d.green ^ 2).mulVec (fun _ ↦ 1) i) := by
  cases s with
  | zero => omega
  | succ n =>
    let e : Fin (n + 1) ≃ Fin (n + 1) := Equiv.swap 0 i
    have hrow (k : ℕ) := d.green_pow_mulVec_one_reindex e k 0
    have he : e 0 = i := Equiv.swap_apply_left 0 i
    simp only [he] at hrow
    have hfirst := hrow 1
    simp only [pow_one] at hfirst
    have hzero := (d.reindex e).green_zero_second_eq_of_third_eq
    rw [hfirst, hrow 2, hrow 3] at hzero
    have hn2 : (n : ℝ) + 1 + 1 = n + 2 := by ring
    have hn3 : (n : ℝ) + 1 + 2 = n + 3 := by ring
    simp only [Nat.cast_add, Nat.cast_one, hn2, hn3] at heq ⊢
    exact hzero heq

end SSPRK.PhaseTypeData
