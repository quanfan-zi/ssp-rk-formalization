import SSPRK.PhaseTypeThirdDefect
import SSPRK.PhaseTypeThirdLaw

/-!
# Equality in the V2.10 defect proof

Vanishing of the six-square certificate forces the normalized first two moments to be
those of the unit-rate Erlang chain. The existing minimum-variance equality theorem
then identifies the law. The mixture step reuses its weighted Cauchy--Schwarz equality
conditions; no independent auxiliary-law comparison is used.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SSPRK.PhaseTypeData

/-- At a fixed normalized start, equality forces minimum variance by the six-square proof. -/
theorem normalizedGreen_second_eq_of_third_eq_defect {n : ℕ} (d : PhaseTypeData (n + 1))
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
      exact (green_moment_class_defect n d.eliminateZero hmean).scale
        (inv_pos.mpr d.green_pivot_pos)
    have hsharp := htail.block_defect_eq_parameters d.normalizedGreen_eta1_nonneg
      (d.normalizedGreen_eta2_nonneg d.normalizedGreen_blockH_nonneg) (by
        rw [phaseBlock_first_moment _ d.normalizedGreen_zero_zero,
          phaseBlock_second_moment _ d.normalizedGreen_zero_zero,
          phaseBlock_third_moment _ d.normalizedGreen_zero_zero] at heq
        convert heq using 1 <;> ring)
    rw [phaseBlock_first_moment _ d.normalizedGreen_zero_zero,
      phaseBlock_second_moment _ d.normalizedGreen_zero_zero,
      hsharp.1, hsharp.2.1, hsharp.2.2.1]
    ring

/-- Undo the Green-pivot scaling in the defect equality argument. -/
theorem green_zero_second_eq_of_third_eq_defect {n : ℕ} (d : PhaseTypeData (n + 1))
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
  have hsharp := d.normalizedGreen_second_eq_of_third_eq_defect hnormalized
  rw [hfirst, hsecond] at hsharp
  apply mul_left_cancel₀ (pow_ne_zero 2 (inv_ne_zero d.green_pivot_pos.ne'))
  nlinarith only [hsharp]

/-- Any fixed initial state can be relabelled as the distinguished state. -/
theorem green_second_eq_of_third_eq_defect {s : ℕ} (d : PhaseTypeData s)
    (hs : 0 < s) (i : Fin s)
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
    have hzero := (d.reindex e).green_zero_second_eq_of_third_eq_defect
    rw [hfirst, hrow 2, hrow 3] at hzero
    have hn2 : (n : ℝ) + 1 + 1 = n + 2 := by ring
    have hn3 : (n : ℝ) + 1 + 2 = n + 3 := by ring
    simp only [Nat.cast_add, Nat.cast_one, hn2, hn3] at heq ⊢
    exact hzero heq

/-- Each fixed-start moment triple satisfies the bound by the new defect induction. -/
theorem green_row_moment_class_defect {s : ℕ} (d : PhaseTypeData s) (i : Fin s) :
    MomentClass s (d.green.mulVec (fun _ ↦ 1) i)
      (2 * (d.green ^ 2).mulVec (fun _ ↦ 1) i)
      (6 * (d.green ^ 3).mulVec (fun _ ↦ 1) i) := by
  cases s with
  | zero => exact Fin.elim0 i
  | succ n =>
    let e : Fin (n + 1) ≃ Fin (n + 1) := Equiv.swap 0 i
    have hzero := (d.reindex e).green_zero_momentClass_of_induction_defect
      (green_moment_class_defect n)
    have hrow (k : ℕ) := d.green_pow_mulVec_one_reindex e k 0
    have he : e 0 = i := Equiv.swap_apply_left 0 i
    simp only [he] at hrow
    have hfirst := hrow 1
    simp only [pow_one] at hfirst
    rw [hfirst, hrow 2, hrow 3] at hzero
    exact hzero

/-- Equality in a finite initial mixture reduces to the new fixed-start equality proof. -/
theorem green_mixture_second_eq_of_third_eq_defect {s : ℕ} (d : PhaseTypeData s)
    (hmean : 0 < dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)))
    (heq : ((s : ℝ) + 2) *
        (2 * dotProduct d.initial ((d.green ^ 2).mulVec (fun _ ↦ 1))) ^ 2 =
      ((s : ℝ) + 1) * dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)) *
        (6 * dotProduct d.initial ((d.green ^ 3).mulVec (fun _ ↦ 1)))) :
    ((s : ℝ) + 1) * dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)) ^ 2 =
      (s : ℝ) * d.mass *
        (2 * dotProduct d.initial ((d.green ^ 2).mulVec (fun _ ↦ 1))) := by
  have hs : 0 < s := by
    cases s with
    | zero => simp [dotProduct] at hmean
    | succ n => exact Nat.succ_pos n
  let m1 := fun i ↦ d.green.mulVec (fun _ ↦ 1) i
  let m2 := fun i ↦ 2 * (d.green ^ 2).mulVec (fun _ ↦ 1) i
  let m3 := fun i ↦ 6 * (d.green ^ 3).mulVec (fun _ ↦ 1) i
  have hclass : ∀ i, MomentClass s (m1 i) (m2 i) (m3 i) := by
    intro i
    exact d.green_row_moment_class_defect i
  have hresult := MomentClass.finite_mixture_second_eq_of_third_eq
    d.initial m1 m2 m3 d.initial_nonneg hclass (by
      simpa only [m1, dotProduct] using hmean) (fun i hi hsharp ↦ by
        exact d.green_second_eq_of_third_eq_defect hs i hsharp) (by
      simpa only [m1, m2, m3, dotProduct, Finset.mul_sum, mul_left_comm] using heq)
  simpa only [m1, m2, dotProduct, mass, Finset.mul_sum, mul_left_comm] using hresult

/-- The defect proof supplies the same mass-corrected chain representation at equality. -/
theorem third_equality_representation_defect {s : ℕ} (d : PhaseTypeData s) (hs : 0 < s)
    (hmean : 0 < dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)))
    (heq : ((s : ℝ) + 2) * (2 * dotProduct d.initial ((d.green ^ 2).mulVec (fun _ ↦ 1))) ^ 2 =
      ((s : ℝ) + 1) * dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)) *
        (6 * dotProduct d.initial ((d.green ^ 3).mulVec (fun _ ↦ 1)))) :
    ∃ a : ℝ, 0 < a ∧ ∃ e : Fin s ≃ Fin s,
      d.transition.submatrix e e = 1 - a⁻¹ • chainD s ∧
      d.green.submatrix e e = a • chainL s ∧
      (∀ j, d.initial (e j) = if j = ⟨s - 1, by omega⟩ then d.mass else 0) ∧
      dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)) = d.mass * (s : ℝ) * a := by
  apply d.mass_second_equality_representation hs hmean
  nlinarith only [d.green_mixture_second_eq_of_third_eq_defect hmean heq]

/-- At defect equality the mean fixes the second moment of the equal-rate chain. -/
theorem third_equality_second_moment_defect {s : ℕ} (d : PhaseTypeData s) (hs : 0 < s)
    (hmean : 0 < dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)))
    (heq : ((s : ℝ) + 2) * (2 * dotProduct d.initial ((d.green ^ 2).mulVec (fun _ ↦ 1))) ^ 2 =
      ((s : ℝ) + 1) * dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)) *
        (6 * dotProduct d.initial ((d.green ^ 3).mulVec (fun _ ↦ 1))))
    (a : ℝ) (hfirst : dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)) =
      d.mass * (s : ℝ) * a) :
    2 * dotProduct d.initial ((d.green ^ 2).mulVec (fun _ ↦ 1)) =
      d.mass * a ^ 2 * (s : ℝ) * ((s : ℝ) + 1) := by
  have hm := d.mass_pos_of_green_mean_pos hmean
  have hsecond := d.green_mixture_second_eq_of_third_eq_defect hmean heq
  rw [hfirst] at hsecond
  apply mul_left_cancel₀ (mul_ne_zero (Nat.cast_ne_zero.mpr hs.ne') hm.ne')
  nlinarith only [hsecond]

/-- The gamma third moment, specialized directly from the general integral formula. -/
theorem integral_cube_gammaMeasure_defect {a κ : ℝ} (ha : 0 < a) (hκ : 0 < κ) :
    ∫ x, x ^ 3 ∂gammaMeasure a κ = a * (a + 1) * (a + 2) / κ ^ 3 := by
  rw [integral_pow_gammaMeasure ha hκ]
  norm_num only [Nat.cast_ofNat]
  rw [show a + 3 = (a + 2) + 1 by ring,
    Real.Gamma_add_one (by positivity : a + 2 ≠ 0),
    show a + 2 = (a + 1) + 1 by ring,
    Real.Gamma_add_one (by positivity : a + 1 ≠ 0), Real.Gamma_add_one ha.ne']
  field_simp

/-- V2.10 third-moment equality is Erlang, through the vanishing-defect variance reduction. -/
theorem third_integral_eq_iff_gamma_defect {s : ℕ} (d : PhaseTypeData s) (hs : 0 < s)
    (hmass : d.mass = 1) (hmean : 0 < ∫ x, x ∂d.measure) :
    ((s : ℝ) + 2) * (∫ x, x ^ 2 ∂d.measure) ^ 2 =
        ((s : ℝ) + 1) * (∫ x, x ∂d.measure) * (∫ x, x ^ 3 ∂d.measure) ↔
      ∃ κ : ℝ, 0 < κ ∧ d.measure = gammaMeasure (s : ℝ) κ := by
  constructor
  · intro heq
    have hmeanGreen : 0 < dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)) := by
      rw [d.integral_id_measure] at hmean
      exact (div_pos_iff_of_pos_right d.rate_pos).mp hmean
    have hsecond := d.green_mixture_second_eq_of_third_eq_defect hmeanGreen
      (d.third_integral_eq_iff_green.mp heq)
    rw [hmass, mul_one] at hsecond
    apply (d.variance_eq_iff_erlang hs hmean).mp
    apply (d.variance_eq_iff_green_moments hs).mpr
    rw [Matrix.mulVec_mulVec, ← pow_two]
    nlinarith only [hsecond]
  · rintro ⟨κ, hκ, hlaw⟩
    have hshape : 0 < (s : ℝ) := Nat.cast_pos.mpr hs
    rw [hlaw, integral_id_gammaMeasure hshape hκ, integral_sq_gammaMeasure hshape hκ,
      integral_cube_gammaMeasure_defect hshape hκ]
    field_simp

end SSPRK.PhaseTypeData
