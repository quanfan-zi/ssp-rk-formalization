import SSPRK.SDIRKOrder

/-!
# The diagonal coefficient in V2.10

The manuscript writes the SDIRK diagonal using `sqrt ((s - 1) / (s + 1))`.
The existing implementation uses `(s - 1) / sqrt (s ^ 2 - 1)`; the following
identity identifies the two expressions on the theorem's domain.
-/

namespace SSPRK.Paper

/-- The two square-root expressions for the third-order SDIRK parameter agree. -/
theorem sdirkQ_eq_sqrt {s : ℕ} (hs : 2 ≤ s) :
    sdirkQ s = Real.sqrt (((s : ℝ) - 1) / ((s : ℝ) + 1)) := by
  have hsreal : (1 : ℝ) < s := by exact_mod_cast (show 1 < s by omega)
  have hsq : sdirkQ s ^ 2 = ((s : ℝ) - 1) / ((s : ℝ) + 1) := by
    unfold sdirkQ
    rw [div_pow, sdirkT_sq hs]
    field_simp [ne_of_gt (sub_pos.mpr hsreal),
      ne_of_gt (by linarith : 0 < (s : ℝ) + 1)]
  exact ((Real.sqrt_eq_iff_eq_sq (by positivity)
    (div_nonneg (sub_nonneg.mpr hsreal.le) (sdirkT_pos hs).le)).2 hsq.symm).symm

/-- The implemented diagonal coefficient is exactly the formula in V2.10. -/
theorem sdirkGamma_eq_paper {s : ℕ} (hs : 2 ≤ s) :
    sdirkGamma s = (1 - Real.sqrt (((s : ℝ) - 1) / ((s : ℝ) + 1))) / 2 := by
  rw [sdirkGamma, sdirkQ_eq_sqrt hs]

end SSPRK.Paper
