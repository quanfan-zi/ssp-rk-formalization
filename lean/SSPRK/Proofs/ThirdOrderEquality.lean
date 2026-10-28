import SSPRK.Proofs.ThirdOrderClassification

/-!
# Equality classification for the third-order SSP bound

The uniqueness part of V2.10 Theorem 5.2: feasibility at the sharp parameter forces
the explicit SDIRK coefficients below, up to simultaneous stage permutation.
This is the necessity direction; attainment of the displayed family is proved separately.
The three chain conditions suffice; the squared-node condition is not assumed.

The proof applies the third-moment equality classification and recovers the original
coefficients by the inverse transform. The chain argument is kept in the internal proof module.
-/

open scoped BigOperators

namespace SSPRK

/-- Equality in the third-order bound determines every coefficient after a stage permutation. -/
theorem third_order_unique_at_radius
    (s : ℕ)
    (hs : 2 ≤ s)
    (A : Matrix (Fin s) (Fin s) ℝ)
    (b : Fin s → ℝ)
    (r : ℝ)
    (hr : r = (s : ℝ) - 1 + Real.sqrt ((s : ℝ) ^ 2 - 1))
    (hinv : (1 + r • A).det ≠ 0)
    -- Chain order conditions.
    (hord1 :
      dotProduct b (fun _ ↦ (1 : ℝ)) = 1)
    (hord2 :
      dotProduct b (Matrix.mulVec A (fun _ ↦ (1 : ℝ))) = 1 / 2)
    (hord3 :
      dotProduct b ((A * A).mulVec (fun _ ↦ (1 : ℝ))) = 1 / 6)
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
        if j < i then 1 / Real.sqrt ((s : ℝ) ^ 2 - 1)
        else if i = j then (1 - ((s : ℝ) - 1) / Real.sqrt ((s : ℝ) ^ 2 - 1)) / 2
        else 0) ∧
      (fun j ↦ b (e j)) = (fun _ ↦ 1 / (s : ℝ)) := by
  -- Apply the internal classification and unfold the family coefficients in the conclusion.
  simpa only [sdirkA, sdirkB, sdirkDelta, sdirkGamma, sdirkQ, sdirkT] using
    (third_order_classification_at_bound hs A b hord1 hord2 hord3
      (show AbsolutelyMonotoneAt A b ((s : ℝ) - 1 + Real.sqrt ((s : ℝ) ^ 2 - 1)) from
        hr ▸ (show AbsolutelyMonotoneAt A b r from ⟨hinv, ham1, ham2, ham3, ham4⟩)))

end SSPRK
