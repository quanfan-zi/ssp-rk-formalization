import SSPRK.PhaseTypeNormalization
import SSPRK.PhaseTypeLawEquality
import SSPRK.PhaseTypeThirdEquality
import SSPRK.PhaseTypeThirdMixtureEquality

/-! Chain and probability-law classifications for sharp third-moment bounds. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace SSPRK.PhaseTypeData

theorem mass_pos_of_green_mean_pos {s : ℕ} (d : PhaseTypeData s)
    (hmean : 0 < dotProduct d.initial (d.green.mulVec (fun _ ↦ 1))) : 0 < d.mass := by
  have hnonneg : 0 ≤ d.mass := Finset.sum_nonneg (fun i _ ↦ d.initial_nonneg i)
  by_contra hnot
  have hz : d.mass = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
  have hi : d.initial = 0 := by
    funext i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ d.initial_nonneg j)).mp hz i
      (Finset.mem_univ i)
  simp only [hi, zero_dotProduct, lt_self_iff_false] at hmean

theorem mass_second_equality_representation {s : ℕ} (d : PhaseTypeData s) (hs : 0 < s)
    (hmean : 0 < dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)))
    (heq : ((s : ℝ) + 1) * (dotProduct d.initial (d.green.mulVec (fun _ ↦ 1))) ^ 2 =
      d.mass * (s : ℝ) * (2 * dotProduct d.initial ((d.green ^ 2).mulVec (fun _ ↦ 1)))) :
    ∃ a : ℝ, 0 < a ∧ ∃ e : Fin s ≃ Fin s,
      d.transition.submatrix e e = 1 - a⁻¹ • chainD s ∧
      d.green.submatrix e e = a • chainL s ∧
      (∀ j, d.initial (e j) = if j = ⟨s - 1, by omega⟩ then d.mass else 0) ∧
      dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)) = d.mass * (s : ℝ) * a := by
  have hm := d.mass_pos_of_green_mean_pos hmean
  let q := d.normalizeInitial hm
  have hleft : (1 - q.transition) * q.green = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr q.transient)
  have hright : q.green * (1 - q.transition) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr q.transient)
  have hpair : dotProduct q.initial (q.green.mulVec (fun _ ↦ 1)) =
      dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)) / d.mass := by
    simpa only [pow_one] using d.normalizeInitial_green_moment hm 1
  have hqmean : 0 < dotProduct q.initial (q.green.mulVec (fun _ ↦ 1)) := by
    rw [hpair]
    exact div_pos hmean hm
  have hqeq : ((s : ℝ) + 1) * (dotProduct q.initial (q.green.mulVec (fun _ ↦ 1))) ^ 2 =
      2 * (s : ℝ) * dotProduct q.initial (q.green.mulVec (q.green.mulVec (fun _ ↦ 1))) := by
    rw [hpair]
    simp only [q, normalizeInitial_initial, normalizeInitial_green, smul_dotProduct,
      smul_eq_mul, Matrix.mulVec_mulVec, ← pow_two]
    field_simp
    nlinarith only [heq]
  obtain ⟨a, ha, e, hP, hN, hi, hμ⟩ :=
    phase_mixture_chain_classification_of_pos hs q.transition q.green q.initial
      q.substochastic (q.substochastic.inv_nonneg q.transient) hleft hright
      q.initial_nonneg q.initial_mass_le hqmean hqeq
  refine ⟨a, ha, e, hP, hN, ?_, ?_⟩
  · intro j
    have h := congrArg (fun t : ℝ ↦ d.mass * t) (hi j)
    change d.mass * (d.mass⁻¹ * d.initial (e j)) = _ at h
    rw [← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul] at h
    simpa only [mul_ite, mul_one, mul_zero] using h
  · rw [hpair] at hμ
    exact (div_eq_iff hm.ne').mp hμ |>.trans (by ring)

/-- A sharp third-moment bound forces an equal-rate chain with a possible atom at zero. -/
theorem third_equality_representation {s : ℕ} (d : PhaseTypeData s) (hs : 0 < s)
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
  nlinarith only [d.green_mixture_second_eq_of_third_eq hmean heq]

/-- The chain scale is determined by the first two moments at third-moment equality. -/
theorem third_equality_second_moment {s : ℕ} (d : PhaseTypeData s) (hs : 0 < s)
    (hmean : 0 < dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)))
    (heq : ((s : ℝ) + 2) * (2 * dotProduct d.initial ((d.green ^ 2).mulVec (fun _ ↦ 1))) ^ 2 =
      ((s : ℝ) + 1) * dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)) *
        (6 * dotProduct d.initial ((d.green ^ 3).mulVec (fun _ ↦ 1))))
    (a : ℝ) (hfirst : dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)) =
      d.mass * (s : ℝ) * a) :
    2 * dotProduct d.initial ((d.green ^ 2).mulVec (fun _ ↦ 1)) =
      d.mass * a ^ 2 * (s : ℝ) * ((s : ℝ) + 1) := by
  have hm := d.mass_pos_of_green_mean_pos hmean
  have hsecond := d.green_mixture_second_eq_of_third_eq hmean heq
  rw [hfirst] at hsecond
  apply mul_left_cancel₀ (mul_ne_zero (Nat.cast_ne_zero.mpr hs.ne') hm.ne')
  nlinarith only [hsecond]

/-- At equality, the law is a mixture of immediate absorption and an Erlang law. -/
theorem measure_eq_atom_add_gamma_of_third_eq {s : ℕ} (d : PhaseTypeData s) (hs : 0 < s)
    (hmean : 0 < dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)))
    (heq : ((s : ℝ) + 2) * (2 * dotProduct d.initial ((d.green ^ 2).mulVec (fun _ ↦ 1))) ^ 2 =
      ((s : ℝ) + 1) * dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)) *
        (6 * dotProduct d.initial ((d.green ^ 3).mulVec (fun _ ↦ 1)))) :
    ∃ κ : ℝ, 0 < κ ∧ d.measure = ENNReal.ofReal (1 - d.mass) • Measure.dirac 0 +
      ENNReal.ofReal d.mass • gammaMeasure (s : ℝ) κ := by
  obtain ⟨a, ha, e, hP, _, hi, _⟩ := d.third_equality_representation hs hmean heq
  have hm := d.mass_pos_of_green_mean_pos hmean
  have hgen : d.generator.submatrix e e = -(d.rate / a) • chainD s := by
    have hid : d.generator.submatrix e e = d.rate • (d.transition.submatrix e e - 1) := by
      ext j k
      simp [generator, Matrix.submatrix, Matrix.one_apply]
    rw [hid, hP, div_eq_mul_inv]
    module
  have hnormalized : (d.normalizeInitial hm).measure = gammaMeasure (s : ℝ) (d.rate / a) := by
    cases s with
    | zero => omega
    | succ n =>
      rw [Nat.cast_add, Nat.cast_one]
      apply (d.normalizeInitial hm).measure_eq_gamma_of_chain
        (d.rate / a) (div_pos d.rate_pos ha) e hgen
      intro j
      change d.mass⁻¹ * d.initial (e j) = _
      rw [hi]
      have hlast : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := by
        ext
        simp
      rw [hlast]
      split_ifs <;> simp only [inv_mul_cancel₀ hm.ne', mul_zero]
  refine ⟨d.rate / a, div_pos d.rate_pos ha, ?_⟩
  rw [d.measure_eq_atom_add_normalizeInitial hm, hnormalized]

/-- The clock rate cancels from the third-moment equality. -/
theorem third_integral_eq_iff_green {s : ℕ} (d : PhaseTypeData s) :
    ((s : ℝ) + 2) * (∫ x, x ^ 2 ∂d.measure) ^ 2 =
        ((s : ℝ) + 1) * (∫ x, x ∂d.measure) * (∫ x, x ^ 3 ∂d.measure) ↔
      ((s : ℝ) + 2) * (2 * dotProduct d.initial ((d.green ^ 2).mulVec (fun _ ↦ 1))) ^ 2 =
        ((s : ℝ) + 1) * dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)) *
          (6 * dotProduct d.initial ((d.green ^ 3).mulVec (fun _ ↦ 1))) := by
  rw [d.integral_id_measure, d.integral_pow_measure 2 (by norm_num),
    d.integral_pow_measure 3 (by norm_num)]
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_ofNat]
  field_simp [d.rate_pos.ne']

private theorem gamma_cube_integral {a κ : ℝ} (ha : 0 < a) (hκ : 0 < κ) :
    ∫ x, x ^ 3 ∂gammaMeasure a κ = a * (a + 1) * (a + 2) / κ ^ 3 := by
  rw [integral_pow_gammaMeasure ha hκ]
  norm_num only [Nat.cast_ofNat]
  rw [show a + 3 = (a + 2) + 1 by ring,
    Real.Gamma_add_one (by positivity : a + 2 ≠ 0),
    show a + 2 = (a + 1) + 1 by ring,
    Real.Gamma_add_one (by positivity : a + 1 ≠ 0), Real.Gamma_add_one ha.ne']
  field_simp

private theorem atom_gamma_power_integral {m a κ : ℝ} (hm : 0 ≤ m) (ha : 0 < a)
    (hκ : 0 < κ) (k : ℕ) (hk : 0 < k) :
    ∫ x, x ^ k ∂(ENNReal.ofReal (1 - m) • Measure.dirac 0 +
      ENNReal.ofReal m • gammaMeasure a κ) = m * ∫ x, x ^ k ∂gammaMeasure a κ := by
  have hint : Integrable (fun x : ℝ ↦ x ^ k) (ENNReal.ofReal m • gammaMeasure a κ) :=
    (integrable_pow_gammaMeasure ha hκ k).smul_measure ENNReal.ofReal_ne_top
  rw [(atom_add_measure_moment (ENNReal.ofReal m • gammaMeasure a κ) (1 - m)
    (fun x : ℝ ↦ x ^ k) hint (zero_pow hk.ne')).2]
  simp only [integral_smul_measure, ENNReal.toReal_ofReal hm, smul_eq_mul]

/-- V1.6 Corollary 4.6: third-moment equality characterizes a zero/Erlang mixture. -/
theorem third_integral_eq_iff_atom_add_gamma {s : ℕ} (d : PhaseTypeData s) (hs : 0 < s)
    (hmean : 0 < ∫ x, x ∂d.measure) :
    ((s : ℝ) + 2) * (∫ x, x ^ 2 ∂d.measure) ^ 2 =
        ((s : ℝ) + 1) * (∫ x, x ∂d.measure) * (∫ x, x ^ 3 ∂d.measure) ↔
      ∃ κ : ℝ, 0 < κ ∧ d.measure = ENNReal.ofReal (1 - d.mass) • Measure.dirac 0 +
        ENNReal.ofReal d.mass • gammaMeasure (s : ℝ) κ := by
  constructor
  · intro heq
    apply d.measure_eq_atom_add_gamma_of_third_eq hs _ (d.third_integral_eq_iff_green.mp heq)
    rw [d.integral_id_measure] at hmean
    exact (div_pos_iff_of_pos_right d.rate_pos).mp hmean
  · rintro ⟨κ, hκ, hlaw⟩
    have hm : 0 ≤ d.mass := Finset.sum_nonneg (fun i _ ↦ d.initial_nonneg i)
    have hshape : 0 < (s : ℝ) := Nat.cast_pos.mpr hs
    have hpower (k : ℕ) (hk : 0 < k) :
        ∫ x, x ^ k ∂d.measure = d.mass * ∫ x, x ^ k ∂gammaMeasure (s : ℝ) κ := by
      rw [hlaw]
      exact atom_gamma_power_integral hm hshape hκ k hk
    have hfirst := hpower 1 (by norm_num)
    simp only [pow_one, integral_id_gammaMeasure hshape hκ] at hfirst
    rw [hfirst, hpower 2 (by norm_num), hpower 3 (by norm_num),
      integral_sq_gammaMeasure hshape hκ, gamma_cube_integral hshape hκ]
    field_simp

end SSPRK.PhaseTypeData
