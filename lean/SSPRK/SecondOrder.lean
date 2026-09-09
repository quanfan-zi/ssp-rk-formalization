import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Linarith

/-!
# 二阶 RK 格式的 SSP 系数上界

当前目标：将用户提供的命题表述为 Lean 定理，并最终证明 `r ≤ 2 * s`。
目前保留 `sorry`，证明尚未完成；与论文 V1.6 的逐项表述核对也尚未完成。
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
  -- 将自然数阶段数的正性转为实数中的正性。
  have hs_real : 0 < (s : ℝ) := by
    exact_mod_cast hs
  -- 待完成：从上面的 RK 假设构造 σ，并证明其范围与矩不等式。
  have hσ_exists : ∃ σ : ℝ,
      (0 < σ ∧ σ ≤ 1) ∧
      1 + 1 / (s : ℝ) ≤ σ * (1 + 2 / r) := by
    sorry
  -- 取出 σ 及其性质，调用已经证明的最后一步。
  obtain ⟨σ, hσ, hbound⟩ := hσ_exists
  exact second_order_bound_of_scalar_inequality (s : ℝ) r σ hs_real hr hσ hbound

end SSPRK
