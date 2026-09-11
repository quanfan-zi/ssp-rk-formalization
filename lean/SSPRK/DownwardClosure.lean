import SSPRK.Feasibility
import SSPRK.RKSubstochastic
import SSPRK.ScaledResolvent

/-!
# Downward closure of absolute monotonicity

Absolute monotonicity at a positive parameter implies absolute monotonicity at every smaller
positive parameter. The proof factors the smaller shifted matrix through a scaled resolvent of
the substochastic matrix at the original parameter.
-/

open scoped BigOperators

namespace SSPRK

noncomputable section

/-- Absolute monotonicity is downward closed on positive parameters. -/
theorem AbsolutelyMonotoneAt.downward_closed {s : ℕ}
    {A : Matrix (Fin s) (Fin s) ℝ} {b : Fin s → ℝ} {r theta : ℝ}
    (ham : AbsolutelyMonotoneAt A b r) (htheta0 : 0 < theta) (hthetar : theta ≤ r) :
    AbsolutelyMonotoneAt A b theta := by
  have hr : 0 < r := lt_of_lt_of_le htheta0 hthetar
  let lam : ℝ := theta / r
  have hlam0 : 0 < lam := div_pos htheta0 hr
  have hlam1 : lam ≤ 1 := (div_le_one hr).mpr hthetar
  have htheta : theta = lam * r := by
    dsimp [lam]
    field_simp
  let P : Matrix (Fin s) (Fin s) ℝ := rkP r A
  let M : Matrix (Fin s) (Fin s) ℝ := rkM r A
  let D : Matrix (Fin s) (Fin s) ℝ := 1 - (1 - lam) • P
  let K : Matrix (Fin s) (Fin s) ℝ := D⁻¹
  have hP : Substochastic P := by
    simpa only [P] using
      rkP_substochastic r A ham.det_ne_zero ham.stages ham.matrix_nonneg
  have hMdet : (1 - P).det ≠ 0 := by
    simpa only [P] using one_sub_rkP_det_ne_zero r A ham.det_ne_zero
  have hc0 : 0 ≤ 1 - lam := sub_nonneg.mpr hlam1
  have hc1 : 1 - lam ≤ 1 := by linarith
  have hDdet : D.det ≠ 0 := by
    simpa only [D] using hP.one_sub_smul_det_ne_zero hMdet hc0 hc1
  have hKnonneg : ∀ i j, 0 ≤ K i j := by
    simpa only [K, D] using hP.one_sub_smul_inv_nonneg hMdet hc0 hc1
  have hDK : D * K = 1 := by
    dsimp only [K]
    exact Matrix.mul_nonsing_inv D (isUnit_iff_ne_zero.mpr hDdet)
  have hKD : K * D = 1 := by
    dsimp only [K]
    exact Matrix.nonsing_inv_mul D (isUnit_iff_ne_zero.mpr hDdet)
  have hMeq : M = 1 - P := by
    simpa only [M, P] using (one_sub_rkP_eq_rkM r A).symm
  have hNM : rkN r A * M = 1 := by
    simpa only [M] using rkN_mul_rkM r A ham.det_ne_zero
  have hNfactor : rkN theta A = rkN r A * D := by
    calc
      rkN theta A = 1 + (lam * r) • A := by rw [rkN, htheta]
      _ = lam • rkN r A + (1 - lam) • 1 := by
        ext i j
        simp [rkN, Matrix.one_apply]
        split_ifs <;> ring
      _ = lam • rkN r A + (1 - lam) • (rkN r A * M) := by rw [hNM]
      _ = rkN r A * D := by
        dsimp only [D]
        rw [hMeq]
        simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, smul_sub]
        module
  have hMD : M * D = D * M := by
    dsimp only [D]
    rw [hMeq]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    module
  have hKM : K * M = M * K := by
    calc
      K * M = (K * M) * (D * K) := by rw [hDK, Matrix.mul_one]
      _ = K * (M * D) * K := by simp only [Matrix.mul_assoc]
      _ = K * (D * M) * K := by rw [hMD]
      _ = (K * D) * (M * K) := by simp only [Matrix.mul_assoc]
      _ = M * K := by rw [hKD, Matrix.one_mul]
  have hNtheta : rkN theta A * (K * M) = 1 := by
    rw [hNfactor]
    calc
      (rkN r A * D) * (K * M) = rkN r A * (D * K) * M := by
        simp only [Matrix.mul_assoc]
      _ = rkN r A * M := by rw [hDK, Matrix.mul_one]
      _ = 1 := hNM
  have hMstage : 0 ≤ Matrix.mulVec M (1 : Fin s → ℝ) := by
    simpa only [M] using ham.stages
  have hstage : 0 ≤ Matrix.mulVec (K * M) (1 : Fin s → ℝ) := by
    rw [← Matrix.mulVec_mulVec]
    intro i
    simp only [Pi.zero_apply, Matrix.mulVec, dotProduct]
    exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (hKnonneg i j) (hMstage j)
  have hDM : D - M = lam • P := by
    dsimp only [D]
    rw [hMeq]
    module
  have hPthetaeq : 1 - K * M = lam • (K * P) := by
    calc
      1 - K * M = K * D - K * M := by rw [hKD]
      _ = K * (D - M) := (Matrix.mul_sub K D M).symm
      _ = K * (lam • P) := by rw [hDM]
      _ = lam • (K * P) := by rw [Matrix.mul_smul]
  have hPtheta : ∀ i j, 0 ≤ (1 - K * M) i j := by
    rw [hPthetaeq]
    intro i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
    exact mul_nonneg hlam0.le
      (Finset.sum_nonneg fun k _ ↦ mul_nonneg (hKnonneg i k) (hP.nonneg k j))
  have hMoutput : 0 ≤ Matrix.vecMul b M := by
    simpa only [M] using ham.output_nonneg
  have houtput : 0 ≤ Matrix.vecMul b (K * M) := by
    rw [hKM, ← Matrix.vecMul_vecMul]
    intro j
    simp only [Pi.zero_apply, Matrix.vecMul, dotProduct]
    exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hMoutput i) (hKnonneg i j)
  have hKrow : lam • Matrix.mulVec K (1 : Fin s → ℝ) ≤ 1 := by
    intro i
    simpa only [K, D, Pi.smul_apply, Pi.one_apply, smul_eq_mul] using
      hP.one_sub_one_sub_smul_inv_mulVec_one_le hMdet hlam0 hlam1 i
  have homega : 0 ≤ r • Matrix.vecMul b M := smul_nonneg hr.le hMoutput
  have homega_mass : dotProduct (r • Matrix.vecMul b M) (1 : Fin s → ℝ) ≤ 1 := by
    have hmass := sub_nonneg.mp ham.output_mass
    simpa only [M, smul_dotProduct, smul_eq_mul] using hmass
  have hweighted :
      dotProduct (r • Matrix.vecMul b M) (lam • Matrix.mulVec K (1 : Fin s → ℝ)) ≤
        dotProduct (r • Matrix.vecMul b M) (1 : Fin s → ℝ) :=
    dotProduct_le_dotProduct_of_nonneg_left hKrow homega
  have hmass :
      theta * dotProduct (Matrix.vecMul b (K * M)) (1 : Fin s → ℝ) ≤ 1 := by
    calc
      theta * dotProduct (Matrix.vecMul b (K * M)) (1 : Fin s → ℝ) =
          dotProduct (r • Matrix.vecMul b M)
            (lam • Matrix.mulVec K (1 : Fin s → ℝ)) := by
        rw [htheta, hKM, ← Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec,
          smul_dotProduct, dotProduct_smul]
        simp only [smul_eq_mul]
        ring
      _ ≤ dotProduct (r • Matrix.vecMul b M) (1 : Fin s → ℝ) := hweighted
      _ ≤ 1 := homega_mass
  refine AbsolutelyMonotoneAt.of_inverse A b theta (K * M) ?_ hstage hPtheta houtput hmass
  simpa only [rkN] using hNtheta

end

end SSPRK
