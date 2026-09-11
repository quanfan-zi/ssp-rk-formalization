import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Linarith
import SSPRK.PhaseMomentBound
import SSPRK.RKSubstochastic

/-!
# 二阶 RK 格式的 SSP 系数上界

由完整绝对单调性条件构造非负 Green 矩阵，利用有限状态的势函数和矩不等式
证明 `r ≤ 2 * s`。对应论文 V1.6 第 2.4、2.6、3 节及定理 5.2 的上界部分。
本文件暂不讨论上界的达到、等号情形或系数唯一性。
-/

open scoped BigOperators

namespace SSPRK

/-- 证明的最后一步：由关于 σ 的数值不等式推出二阶上界。 -/
lemma second_order_bound_of_scalar_inequality
    (s r σ : ℝ)
    (hs : 0 < s)
    (hr : 0 < r)
    (hσ : 0 < σ ∧ σ ≤ 1)
    (hbound : 1 + 1 / s ≤ σ * (1 + 2 / r)) :
    r ≤ 2 * s := by
  -- 因子 1 + 2/r 非负，所以可将 σ ≤ 1 的两边同乘这个因子。
  have hfactor : 0 ≤ 1 + 2 / r :=
    add_nonneg zero_le_one (div_nonneg zero_le_two hr.le)
  have hupper : σ * (1 + 2 / r) ≤ 1 + 2 / r := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hσ.2 hfactor
  -- 合并上下界，并消去两边的 1。
  have hreciprocal : 1 / s ≤ 2 / r := by
    linarith [hbound.trans hupper]
  -- s、r 都为正，可以交叉相乘。
  have hcross : 1 * r ≤ 2 * s := (div_le_div_iff₀ hs hr).mp hreciprocal
  simpa only [one_mul] using hcross

/-- The denominator-free final step for the subprobability moment bound. -/
lemma second_order_bound_of_weighted_moment_inequality
    (s r : ℝ) (hr : 0 < r)
    (hbound : (s + 1) * r ^ 2 ≤ 2 * s * (r + r ^ 2 / 2)) : r ≤ 2 * s := by
  nlinarith

theorem second_order_rk_ssp_bound
    (s : ℕ)
    (hs : 0 < s)
    (A : Matrix (Fin s) (Fin s) ℝ)
    (b : Fin s → ℝ)
    (r : ℝ)
    (hr : 0 < r)
    (hinv : (1 + r • A).det ≠ 0)
    -- Second-order conditions.
    (hord1 :
      dotProduct b (fun _ => (1 : ℝ)) = 1)
    (hord2 :
      dotProduct b (Matrix.mulVec A (fun _ => (1 : ℝ))) = (1 : ℝ) / 2)
    -- Four absolute-monotonicity conditions.
    (ham1 :
      0 ≤ Matrix.mulVec ((1 + r • A)⁻¹) (fun _ => (1 : ℝ)))
    (ham2 :
      ∀ i j : Fin s, 0 ≤ (r • (A * (1 + r • A)⁻¹)) i j)
    (ham3 :
      0 ≤ Matrix.vecMul b ((1 + r • A)⁻¹))
    (ham4 :
      0 ≤ 1 - r * dotProduct
        (Matrix.vecMul b ((1 + r • A)⁻¹)) (fun _ => (1 : ℝ))) :
    r ≤ 2 * (s : ℝ) := by
  have hP : Substochastic (rkP r A) := rkP_substochastic r A hinv ham1 ham2
  have hN : MatrixNonneg (rkN r A) := rkN_nonneg r A hinv hP
  have hω : 0 ≤ rkOmega r b A := rkOmega_nonneg r b A hr.le ham3
  have hmass : ∑ i, rkOmega r b A i ≤ 1 := by
    simpa [rkSigma, ones, dotProduct] using rkSigma_le_one r b A ham4
  have hleft : (1 - rkP r A) * rkN r A = 1 := by
    rw [one_sub_rkP_eq_rkM]
    exact rkM_mul_rkN r A hinv
  have hright : rkN r A * (1 - rkP r A) = 1 := by
    rw [one_sub_rkP_eq_rkM]
    exact rkN_mul_rkM r A hinv
  have hbound := phase_second_moment_bound s hs (rkP r A) (rkN r A)
    (rkOmega r b A) hP hN hleft hright hω hmass
  have hfirst : dotProduct (rkOmega r b A) ((rkN r A).mulVec (ones s)) = r := by
    rw [Matrix.dotProduct_mulVec]
    exact rkOmega_N_ones_eq r b A hinv hord1
  have hsecond : dotProduct (rkOmega r b A)
      ((rkN r A).mulVec ((rkN r A).mulVec (ones s))) = r + r ^ 2 / 2 := by
    rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    exact rkOmega_N_sq_ones_eq r b A hinv hord1 hord2
  change ((s : ℝ) + 1) *
    (dotProduct (rkOmega r b A) ((rkN r A).mulVec (ones s))) ^ 2 ≤
      2 * (s : ℝ) * dotProduct (rkOmega r b A)
        ((rkN r A).mulVec ((rkN r A).mulVec (ones s))) at hbound
  rw [hfirst, hsecond] at hbound
  exact second_order_bound_of_weighted_moment_inequality s r hr hbound

end SSPRK
