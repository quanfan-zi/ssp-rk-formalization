import ThirdOrderBound

/-! # The complete third-order radius bound -/

namespace SSPRK

/-- The third-order bound extends to the full supremum defining the complete SSP radius. -/
theorem third_order_radius_bound {s : ℕ} (hs : 2 ≤ s)
    (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ)
    (hord1 : dotProduct b (fun _ ↦ (1 : ℝ)) = 1)
    (hord2 : dotProduct b (A.mulVec (fun _ ↦ (1 : ℝ))) = 1 / 2)
    (hord3 : dotProduct b ((A * A).mulVec (fun _ ↦ (1 : ℝ))) = 1 / 6) :
    absoluteMonotonicityRadius A b ≤
      ENNReal.ofReal ((s : ℝ) - 1 + Real.sqrt ((s : ℝ) ^ 2 - 1)) := by
  apply iSup_le
  intro r
  apply iSup_le
  intro hr
  apply ENNReal.ofReal_le_ofReal
  rcases hr with rfl | ⟨hr, h⟩
  · have hs' : (2 : ℝ) ≤ s := by exact_mod_cast hs
    linarith [Real.sqrt_nonneg ((s : ℝ) ^ 2 - 1)]
  · exact third_order_rk_ssp_bound s hs A b r hr h.det_ne_zero hord1 hord2 hord3
      h.stages h.matrix_nonneg h.output_nonneg h.output_mass

end SSPRK
