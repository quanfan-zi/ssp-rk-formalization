import SSPRK.Substochastic

/-!
# Algebraic phase-variance bound

This file isolates the finite-matrix core of the minimum-variance argument used for the
second-order SSP Runge--Kutta bound.  The potential assumptions are supplied separately by
the state-count argument.
-/

open scoped BigOperators

namespace SSPRK

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A subprobability-weighted mean has square at most its weighted second moment. -/
lemma weighted_mean_sq_le_second_moment (π x : ι → ℝ)
    (hπ_nonneg : ∀ i, 0 ≤ π i) (hπ_sum_le : ∑ i, π i ≤ 1) :
    (dotProduct π x) ^ 2 ≤ dotProduct π (fun i ↦ x i ^ 2) := by
  have hsecond_nonneg : 0 ≤ ∑ i, π i * x i ^ 2 := by
    exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hπ_nonneg i) (sq_nonneg (x i))
  have hcauchy :
      (∑ i, π i * x i) ^ 2 ≤ (∑ i, π i) * ∑ i, π i * x i ^ 2 := by
    simpa using
      (Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset ι)
        (r := fun i ↦ π i * x i) (f := π) (g := fun i ↦ π i * x i ^ 2)
        (fun i _ ↦ hπ_nonneg i)
        (fun i _ ↦ mul_nonneg (hπ_nonneg i) (sq_nonneg (x i)))
        (fun i _ ↦ by ring_nf; exact le_rfl))
  calc
    (dotProduct π x) ^ 2 = (∑ i, π i * x i) ^ 2 := rfl
    _ ≤ (∑ i, π i) * ∑ i, π i * x i ^ 2 := hcauchy
    _ ≤ 1 * ∑ i, π i * x i ^ 2 :=
      mul_le_mul_of_nonneg_right hπ_sum_le hsecond_nonneg
    _ = dotProduct π (fun i ↦ x i ^ 2) := by simp [dotProduct]

/-- Pointwise matrix form of the phase-variance estimate, assuming a state-count potential. -/
theorem phase_variance_pointwise_of_potential
    (P N : Matrix ι ι ℝ) (f : ι → ℝ) (k : ℝ)
    (hP : Substochastic P)
    (hN_nonneg : ∀ i j, 0 ≤ N i j)
    (hk : 0 ≤ k)
    (hleft : (1 - P) * N = 1)
    (hright : N * (1 - P) = 1)
    (hf_lower : ∀ i, (Matrix.mulVec N (fun _ : ι ↦ (1 : ℝ)) i) ^ 2 ≤ k * f i)
    (hf_upper : ∀ i, f i ≤ (Matrix.mulVec N (fun _ : ι ↦ (1 : ℝ)) i) ^ 2)
    (hf_lipschitz : ∀ i j,
      f i - f j ≤ (Matrix.mulVec N (fun _ : ι ↦ (1 : ℝ)) i -
        Matrix.mulVec N (fun _ : ι ↦ (1 : ℝ)) j) ^ 2) :
    ∀ i,
      (k + 1) * (Matrix.mulVec N (fun _ : ι ↦ (1 : ℝ)) i) ^ 2 ≤
        2 * k * Matrix.mulVec N (Matrix.mulVec N (fun _ : ι ↦ (1 : ℝ))) i := by
  let e : ι → ℝ := fun _ ↦ 1
  let m : ι → ℝ := Matrix.mulVec N e
  let m2 : ι → ℝ := fun i ↦ m i ^ 2
  have hAm : Matrix.mulVec (1 - P) m = e := by
    dsimp only [m]
    rw [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
  have hm (i : ι) : m i - ∑ j, P i j * m j = 1 := by
    have hi := congrFun hAm i
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hi
    simpa [Matrix.mulVec, dotProduct, e] using hi
  have hstep (i : ι) :
      Matrix.mulVec (1 - P) f i ≤
        (((2 : ℝ) • m - Matrix.mulVec (1 - P) m2 : ι → ℝ)) i := by
    have hdeficit :
        (1 - ∑ j, P i j) * f i ≤ (1 - ∑ j, P i j) * m i ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · simpa [m, e] using hf_upper i
      · exact sub_nonneg.mpr (hP.row_sum_le i)
    have hdiff :
        ∑ j, P i j * (f i - f j) ≤ ∑ j, P i j * (m i - m j) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left
      · simpa [m, e] using hf_lipschitz i j
      · exact hP.nonneg i j
    calc
      Matrix.mulVec (1 - P) f i =
          (1 - ∑ j, P i j) * f i + ∑ j, P i j * (f i - f j) := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]
        change f i - ∑ j, P i j * f j = _
        simp_rw [mul_sub, Finset.sum_sub_distrib]
        rw [← Finset.sum_mul]
        ring
      _ ≤ (1 - ∑ j, P i j) * m i ^ 2 +
          ∑ j, P i j * (m i - m j) ^ 2 := add_le_add hdeficit hdiff
      _ = (((2 : ℝ) • m - Matrix.mulVec (1 - P) m2 : ι → ℝ)) i := by
        have hPm : ∑ j, P i j * m j = m i - 1 := by linarith [hm i]
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]
        change (1 - ∑ j, P i j) * m i ^ 2 + ∑ j, P i j * (m i - m j) ^ 2 =
          2 * m i - (m i ^ 2 - ∑ j, P i j * m j ^ 2)
        simp_rw [sub_sq]
        simp_rw [mul_add, mul_sub]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [← Finset.sum_mul]
        have hcross : ∑ j, P i j * (2 * m i * m j) =
            2 * m i * ∑ j, P i j * m j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        rw [hcross, hPm]
        nlinarith
  have hpreserve (i : ι) :
      Matrix.mulVec N (Matrix.mulVec (1 - P) f) i ≤
        Matrix.mulVec N ((2 : ℝ) • m - Matrix.mulVec (1 - P) m2) i := by
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_le_sum fun j _ ↦
      mul_le_mul_of_nonneg_left (hstep j) (hN_nonneg i j)
  have hNAf : Matrix.mulVec N (Matrix.mulVec (1 - P) f) = f := by
    rw [Matrix.mulVec_mulVec, hright, Matrix.one_mulVec]
  have hNm2 : Matrix.mulVec N (Matrix.mulVec (1 - P) m2) = m2 := by
    rw [Matrix.mulVec_mulVec, hright, Matrix.one_mulVec]
  intro i
  have hfv : f i ≤ 2 * Matrix.mulVec N m i - m i ^ 2 := by
    calc
      f i = Matrix.mulVec N (Matrix.mulVec (1 - P) f) i := by rw [hNAf]
      _ ≤ Matrix.mulVec N ((2 : ℝ) • m - Matrix.mulVec (1 - P) m2) i := hpreserve i
      _ = 2 * Matrix.mulVec N m i - m i ^ 2 := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hNm2]
        simp [m2]
  have hlower : m i ^ 2 ≤ k * f i := by simpa [m, e] using hf_lower i
  have hscaled : k * f i ≤ k * (2 * Matrix.mulVec N m i - m i ^ 2) :=
    mul_le_mul_of_nonneg_left hfv hk
  dsimp only [m, e] at hlower hscaled ⊢
  nlinarith

/-- The first two phase moments satisfy the minimum-variance inequality once a potential
with the state-count bounds is available. -/
theorem phase_second_moment_bound_of_potential
    (P N : Matrix ι ι ℝ) (π f : ι → ℝ) (k : ℝ)
    (hP : Substochastic P)
    (hN_nonneg : ∀ i j, 0 ≤ N i j)
    (hk : 0 ≤ k)
    (hleft : (1 - P) * N = 1)
    (hright : N * (1 - P) = 1)
    (hπ_nonneg : ∀ i, 0 ≤ π i)
    (hπ_sum_le : ∑ i, π i ≤ 1)
    (hf_lower : ∀ i, (Matrix.mulVec N (fun _ : ι ↦ (1 : ℝ)) i) ^ 2 ≤ k * f i)
    (hf_upper : ∀ i, f i ≤ (Matrix.mulVec N (fun _ : ι ↦ (1 : ℝ)) i) ^ 2)
    (hf_lipschitz : ∀ i j,
      f i - f j ≤ (Matrix.mulVec N (fun _ : ι ↦ (1 : ℝ)) i -
        Matrix.mulVec N (fun _ : ι ↦ (1 : ℝ)) j) ^ 2) :
    (k + 1) * (dotProduct π (Matrix.mulVec N (fun _ : ι ↦ (1 : ℝ)))) ^ 2 ≤
      2 * k * dotProduct π (Matrix.mulVec N (Matrix.mulVec N (fun _ : ι ↦ (1 : ℝ)))) := by
  let e : ι → ℝ := fun _ ↦ 1
  let m : ι → ℝ := Matrix.mulVec N e
  let n : ι → ℝ := Matrix.mulVec N m
  have hpoint : ∀ i, (k + 1) * m i ^ 2 ≤ 2 * k * n i := by
    simpa [m, n, e] using
      (phase_variance_pointwise_of_potential P N f k hP hN_nonneg hk hleft hright
        hf_lower hf_upper hf_lipschitz)
  have hweighted :
      (k + 1) * dotProduct π (fun i ↦ m i ^ 2) ≤ 2 * k * dotProduct π n := by
    change (k + 1) * (∑ i, π i * m i ^ 2) ≤ 2 * k * ∑ i, π i * n i
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hi := mul_le_mul_of_nonneg_left (hpoint i) (hπ_nonneg i)
    nlinarith
  have hcauchy : (dotProduct π m) ^ 2 ≤ dotProduct π (fun i ↦ m i ^ 2) :=
    weighted_mean_sq_le_second_moment π m hπ_nonneg hπ_sum_le
  calc
    (k + 1) * (dotProduct π (Matrix.mulVec N (fun _ : ι ↦ (1 : ℝ)))) ^ 2 =
        (k + 1) * (dotProduct π m) ^ 2 := by rfl
    _ ≤ (k + 1) * dotProduct π (fun i ↦ m i ^ 2) :=
      mul_le_mul_of_nonneg_left hcauchy (by linarith)
    _ ≤ 2 * k * dotProduct π n := hweighted
    _ = 2 * k * dotProduct π
        (Matrix.mulVec N (Matrix.mulVec N (fun _ : ι ↦ (1 : ℝ)))) := by rfl

end SSPRK
