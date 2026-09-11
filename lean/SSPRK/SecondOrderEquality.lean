import SSPRK.Radius

/-!
# Initial-weight rigidity at the optimal second-order radius

At radius twice the stage count, the transformed output has mass one and is supported
on states whose Green-matrix row sum equals that radius.
-/

open scoped BigOperators

namespace SSPRK

/-- Equality in the subprobability second-moment bound fixes mass and support. -/
lemma weighted_second_moment_equality {ι : Type*} [Fintype ι]
    (π x : ι → ℝ) (a : ℝ) (ha : 0 < a)
    (hπ : ∀ i, 0 ≤ π i) (hmass : ∑ i, π i ≤ 1)
    (hmean : dotProduct π x = a)
    (hsecond : dotProduct π (fun i ↦ x i ^ 2) ≤ a ^ 2) :
    (∑ i, π i = 1) ∧ ∀ i, 0 < π i → x i = a := by
  have hvariance :
      ∑ i, π i * (x i - a) ^ 2 =
        dotProduct π (fun i ↦ x i ^ 2) - 2 * a ^ 2 + a ^ 2 * ∑ i, π i := by
    calc
      _ = (∑ i, π i * x i ^ 2) - 2 * a * (∑ i, π i * x i) +
          a ^ 2 * ∑ i, π i := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [show ∑ i, π i * x i = a from hmean]
        simp only [dotProduct]
        ring
  have hterm : ∀ i, 0 ≤ π i * (x i - a) ^ 2 :=
    fun i ↦ mul_nonneg (hπ i) (sq_nonneg _)
  have hnonneg : 0 ≤ ∑ i, π i * (x i - a) ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ hterm i
  have hmass_eq : ∑ i, π i = 1 := by
    have hapos : 0 < a ^ 2 := sq_pos_of_pos ha
    nlinarith
  have hzero : ∑ i, π i * (x i - a) ^ 2 = 0 := by
    rw [hmass_eq] at hvariance
    linarith
  refine ⟨hmass_eq, ?_⟩
  intro i hi
  have hi_zero := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ hterm j)).mp hzero
    i (Finset.mem_univ i)
  have hsquare : (x i - a) ^ 2 = 0 := (mul_eq_zero.mp hi_zero).resolve_left hi.ne'
  nlinarith [sq_nonneg (x i - a)]

/-- Optimal second-order tableaux have full transformed output mass, supported on
states of maximal mean lifetime. -/
theorem second_order_optimal_initial_weights {s : ℕ} (hs : 0 < s)
    (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ) (r : ℝ)
    (hr : r = 2 * (s : ℝ))
    (hord1 : dotProduct b (ones s) = 1)
    (hord2 : dotProduct b (A.mulVec (ones s)) = 1 / 2)
    (ham : AbsolutelyMonotoneAt A b r) :
    rkSigma r b A = 1 ∧
      ∀ i, 0 < rkOmega r b A i → (rkN r A).mulVec (ones s) i = r := by
  have hspos : 0 < (s : ℝ) := Nat.cast_pos.mpr hs
  have hrpos : 0 < r := by rw [hr]; positivity
  have hP : Substochastic (rkP r A) :=
    rkP_substochastic r A ham.det_ne_zero ham.stages ham.matrix_nonneg
  have hN : MatrixNonneg (rkN r A) := rkN_nonneg r A ham.det_ne_zero hP
  have hω : 0 ≤ rkOmega r b A := rkOmega_nonneg r b A hrpos.le ham.output_nonneg
  have hmass : ∑ i, rkOmega r b A i ≤ 1 := by
    simpa [rkSigma, ones, dotProduct] using rkSigma_le_one r b A ham.output_mass
  have hleft : (1 - rkP r A) * rkN r A = 1 := by
    rw [one_sub_rkP_eq_rkM]
    exact rkM_mul_rkN r A ham.det_ne_zero
  have hright : rkN r A * (1 - rkP r A) = 1 := by
    rw [one_sub_rkP_eq_rkM]
    exact rkN_mul_rkM r A ham.det_ne_zero
  have hfirst : dotProduct (rkOmega r b A) ((rkN r A).mulVec (ones s)) = r := by
    rw [Matrix.dotProduct_mulVec]
    exact rkOmega_N_ones_eq r b A ham.det_ne_zero hord1
  have hsecond : dotProduct (rkOmega r b A)
      ((rkN r A).mulVec ((rkN r A).mulVec (ones s))) = r + r ^ 2 / 2 := by
    rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    exact rkOmega_N_sq_ones_eq r b A ham.det_ne_zero hord1 hord2
  let m := (rkN r A).mulVec (ones s)
  have hm : ∀ i, 0 ≤ m i := by
    intro i
    change 0 ≤ ∑ j, rkN r A i j * 1
    exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (hN i j) zero_le_one
  obtain ⟨f, _, hlower, hupper, hdiff⟩ := exists_variance_potential s m hm
  have hpoint : ∀ i, ((s : ℝ) + 1) * m i ^ 2 ≤
      2 * (s : ℝ) * (rkN r A).mulVec m i :=
    phase_variance_pointwise_of_potential (rkP r A) (rkN r A) f s hP hN hspos.le
      hleft hright hlower hupper hdiff
  have hweighted : ((s : ℝ) + 1) * dotProduct (rkOmega r b A) (fun i ↦ m i ^ 2) ≤
      2 * (s : ℝ) * dotProduct (rkOmega r b A) ((rkN r A).mulVec m) := by
    simp only [dotProduct, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    nlinarith only [mul_le_mul_of_nonneg_left (hpoint i) (hω i)]
  have hsq : dotProduct (rkOmega r b A) (fun i ↦ m i ^ 2) ≤ r ^ 2 := by
    change dotProduct (rkOmega r b A) ((rkN r A).mulVec m) = _ at hsecond
    rw [hsecond] at hweighted
    have hidentity : 2 * (s : ℝ) * (r + r ^ 2 / 2) = ((s : ℝ) + 1) * r ^ 2 := by
      rw [hr]
      ring
    rw [hidentity] at hweighted
    exact (mul_le_mul_iff_right₀ (by positivity : 0 < (s : ℝ) + 1)).mp hweighted
  obtain ⟨hmass_eq, hsupport⟩ :=
    weighted_second_moment_equality (rkOmega r b A) m r hrpos hω hmass hfirst hsq
  exact ⟨by simpa [rkSigma, dotProduct, ones] using hmass_eq, hsupport⟩

end SSPRK
