import SSPRK.Proofs.SecondOrderClassification

/-!
# Equality classification for the second-order SSP bound

The uniqueness part of V2.10 Theorem 5.1: feasibility at the sharp parameter forces
the explicit repeated midpoint coefficients below, up to simultaneous stage permutation.
This is the necessity direction; attainment of the displayed family is proved separately.

The proof applies the variance equality classification and recovers the original
coefficients by the inverse transform. The chain argument is kept in the internal proof module.
-/

open scoped BigOperators

namespace SSPRK

/-- Equality in the second-order bound determines every coefficient after a stage permutation. -/
theorem second_order_unique_at_twice_stages
    (s : ℕ)
    (hs : 0 < s)
    (A : Matrix (Fin s) (Fin s) ℝ)
    (b : Fin s → ℝ)
    (r : ℝ)
    (hr : r = 2 * (s : ℝ))
    (hinv : (1 + r • A).det ≠ 0)
    -- Second-order conditions.
    (hord1 :
      dotProduct b (fun _ ↦ (1 : ℝ)) = 1)
    (hord2 :
      dotProduct b (Matrix.mulVec A (fun _ ↦ (1 : ℝ))) = 1 / 2)
    -- Four absolute-monotonicity conditions.
    (ham1 :
      0 ≤ Matrix.mulVec ((1 + r • A)⁻¹) (fun _ ↦ (1 : ℝ)))
    (ham2 :
      ∀ i j : Fin s, 0 ≤ (r • (A * (1 + r • A)⁻¹)) i j)
    (ham3 :
      0 ≤ Matrix.vecMul b ((1 + r • A)⁻¹))
    (ham4 :
      0 ≤ 1 - r * dotProduct
        (Matrix.vecMul b ((1 + r • A)⁻¹)) (fun _ ↦ (1 : ℝ))) :
    ∃ e : Fin s ≃ Fin s,
      A.submatrix e e = (fun i j ↦
        if j < i then 1 / (s : ℝ) else if i = j then 1 / (2 * (s : ℝ)) else 0) ∧
      (fun j ↦ b (e j)) = (fun _ ↦ 1 / (s : ℝ)) := by
  -- Apply the internal classification and unfold the family coefficients in the conclusion.
  simpa only [midpointA, midpointB, ones] using
    (second_order_classification_at_bound hs A b hord1 hord2
      (hr ▸ (show AbsolutelyMonotoneAt A b r from ⟨hinv, ham1, ham2, ham3, ham4⟩)))

end SSPRK
