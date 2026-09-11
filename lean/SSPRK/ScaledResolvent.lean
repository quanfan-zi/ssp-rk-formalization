import SSPRK.Substochastic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Scaled resolvents of substochastic matrices

Scaling a substochastic matrix by a factor in `[0, 1]` preserves substochasticity. If the
original Green matrix exists, the scaled geometric series converges, so every scaled
resolvent is nonsingular and has an entrywise nonnegative inverse.
-/

open scoped BigOperators

namespace SSPRK

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Substochastic

omit [DecidableEq ι] in
/-- Scaling by a factor in `[0, 1]` preserves substochasticity. -/
theorem smul {P : Matrix ι ι ℝ} (hP : Substochastic P) {c : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) : Substochastic (c • P) := by
  constructor
  · intro i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact mul_nonneg hc0 (hP.nonneg i j)
  · intro i
    simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    calc
      c * ∑ j, P i j ≤ c * 1 := mul_le_mul_of_nonneg_left (hP.row_sum_le i) hc0
      _ ≤ 1 := by simpa using hc1

/-- Powers of a scaled matrix are bounded entrywise by the corresponding unscaled powers. -/
theorem smul_pow_entry_le {P : Matrix ι ι ℝ} (hP : Substochastic P) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) (i j : ι) :
    ((c • P) ^ n) i j ≤ (P ^ n) i j := by
  rw [smul_pow, Matrix.smul_apply, smul_eq_mul]
  calc
    c ^ n * (P ^ n) i j ≤ 1 * (P ^ n) i j :=
      mul_le_mul_of_nonneg_right (pow_le_one₀ hc0 hc1) ((hP.pow n).nonneg i j)
    _ = (P ^ n) i j := one_mul _

/-- The geometric series of every scaling in `[0, 1]` converges. -/
theorem summable_smul_pow {P : Matrix ι ι ℝ} (hP : Substochastic P)
    (hinv : (1 - P).det ≠ 0) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    Summable (fun n : ℕ ↦ (c • P) ^ n) := by
  apply Pi.summable.mpr
  intro i
  apply Pi.summable.mpr
  intro j
  apply Summable.of_nonneg_of_le
  · intro n
    exact ((hP.smul hc0 hc1).pow n).nonneg i j
  · intro n
    exact hP.smul_pow_entry_le hc0 hc1 n i j
  · exact Pi.summable.mp (Pi.summable.mp (hP.summable_pow hinv) i) j

/-- Every scaling in `[0, 1]` has a nonsingular resolvent. -/
theorem one_sub_smul_det_ne_zero {P : Matrix ι ι ℝ} (hP : Substochastic P)
    (hinv : (1 - P).det ≠ 0) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (1 - c • P).det ≠ 0 := by
  exact Matrix.det_ne_zero_of_right_inverse
    (hP.summable_smul_pow hinv hc0 hc1).one_sub_mul_tsum_pow

/-- Every scaled resolvent has an entrywise nonnegative inverse. -/
theorem one_sub_smul_inv_nonneg {P : Matrix ι ι ℝ} (hP : Substochastic P)
    (hinv : (1 - P).det ≠ 0) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∀ i j, 0 ≤ ((1 - c • P)⁻¹) i j := by
  exact (hP.smul hc0 hc1).inv_nonneg (hP.one_sub_smul_det_ne_zero hinv hc0 hc1)

/-- The rows of the scaled Green matrix have sum at most `1 / λ`. -/
theorem one_sub_one_sub_smul_inv_mulVec_one_le {P : Matrix ι ι ℝ}
    (hP : Substochastic P) (hinv : (1 - P).det ≠ 0) {lam : ℝ} (hlam0 : 0 < lam)
    (hlam1 : lam ≤ 1) (i : ι) :
    lam * Matrix.mulVec ((1 - (1 - lam) • P)⁻¹) (1 : ι → ℝ) i ≤ 1 := by
  have hc0 : 0 ≤ 1 - lam := sub_nonneg.mpr hlam1
  have hc1 : 1 - lam ≤ 1 := by linarith
  have hPone : Matrix.mulVec P (1 : ι → ℝ) ≤ 1 := by
    intro j
    simpa [Matrix.mulVec, dotProduct] using hP.row_sum_le j
  have hDone : lam • (1 : ι → ℝ) ≤
      Matrix.mulVec (1 - (1 - lam) • P) (1 : ι → ℝ) := by
    intro j
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
    simp only [Pi.smul_apply, Pi.one_apply, Pi.sub_apply, smul_eq_mul]
    have hj := mul_le_mul_of_nonneg_left (hPone j) hc0
    norm_num at hj ⊢
    linarith
  have hdet : (1 - (1 - lam) • P).det ≠ 0 :=
    hP.one_sub_smul_det_ne_zero hinv hc0 hc1
  have hGnonneg : ∀ j k, 0 ≤ ((1 - (1 - lam) • P)⁻¹) j k :=
    hP.one_sub_smul_inv_nonneg hinv hc0 hc1
  have hmul :
      Matrix.mulVec ((1 - (1 - lam) • P)⁻¹) (lam • (1 : ι → ℝ)) ≤
        Matrix.mulVec ((1 - (1 - lam) • P)⁻¹)
          (Matrix.mulVec (1 - (1 - lam) • P) (1 : ι → ℝ)) := by
    intro j
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_left (hDone k) (hGnonneg j k)
  have hcancel :
      Matrix.mulVec ((1 - (1 - lam) • P)⁻¹)
          (Matrix.mulVec (1 - (1 - lam) • P) (1 : ι → ℝ)) = 1 := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  have hi := hmul i
  rw [hcancel] at hi
  simpa only [Matrix.mulVec_smul, Pi.smul_apply, Pi.one_apply, smul_eq_mul] using hi

end Substochastic
end SSPRK
