import SSPRK.Radius

/-!
# Certificates for complete absolute monotonicity

An explicit inverse can certify all tableau inequalities without computing a symbolic inverse.
-/

namespace SSPRK

open scoped ENNReal

/-- A positive feasible parameter is a lower bound for the complete tableau radius. -/
theorem AbsolutelyMonotoneAt.le_radius {s : ℕ}
    {A : Matrix (Fin s) (Fin s) ℝ} {b : Fin s → ℝ} {r : ℝ}
    (h : AbsolutelyMonotoneAt A b r) (hr : 0 < r) :
    ENNReal.ofReal r ≤ absoluteMonotonicityRadius A b := by
  exact le_iSup_of_le r (le_iSup_of_le (show r ∈ feasibleRadii A b from Or.inr ⟨hr, h⟩)
    le_rfl)

/-- Certify feasibility from an inverse and the nonnegative transformed coefficients. -/
theorem AbsolutelyMonotoneAt.of_inverse {s : ℕ}
    (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ) (r : ℝ)
    (M : Matrix (Fin s) (Fin s) ℝ)
    (hNM : (1 + r • A) * M = 1)
    (hstage : 0 ≤ M.mulVec (fun _ ↦ (1 : ℝ)))
    (hP : ∀ i j, 0 ≤ (1 - M) i j)
    (houtput : 0 ≤ Matrix.vecMul b M)
    (hmass : r * dotProduct (Matrix.vecMul b M) (fun _ ↦ (1 : ℝ)) ≤ 1) :
    AbsolutelyMonotoneAt A b r := by
  have hinv : (1 + r • A)⁻¹ = M := Matrix.inv_eq_right_inv hNM
  have htransform : r • (A * M) = 1 - M := by
    calc
      _ = (1 + r • A) * M - M := by noncomm_ring
      _ = _ := by rw [hNM]
  refine ⟨Matrix.det_ne_zero_of_right_inverse hNM, ?_, ?_, ?_, ?_⟩
  · simpa only [hinv] using hstage
  · simpa only [hinv, htransform] using hP
  · simpa only [hinv] using houtput
  · simpa only [hinv] using sub_nonneg.mpr hmass

end SSPRK
