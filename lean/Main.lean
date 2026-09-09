import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

-- 入门及环境检查示例；尚未形式化论文 V1.6 中的命题。
#eval 1 + 1

example (x : ℝ) : x + 0 = x := by
  simp

example (x : ℝ) (h : x ≥ 1) : x ≥ 0 := by
  linarith
