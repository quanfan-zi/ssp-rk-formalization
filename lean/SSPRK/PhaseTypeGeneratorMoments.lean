import SSPRK.PhaseTypeAllMoments
import SSPRK.PhaseTypeGenerator
import SSPRK.PhaseTypeUniformization

/-!
# PH moments in terms of the transient generator

The integral formula depends only on the initial row and the generator, with no
uniformizing clock rate in its conclusion. This does not assert equality of measures.
-/

open MeasureTheory
open scoped BigOperators

namespace SSPRK

namespace PhaseTypeData

variable {s : ℕ} (d : PhaseTypeData s)

/-- Every positive PH moment is a factorial times a continuous Green-matrix moment. -/
theorem integral_pow_eq_continuousGreen (k : ℕ) (hk : 0 < k) :
    ∫ x, x ^ k ∂d.measure =
      (k.factorial : ℝ) *
        dotProduct d.initial ((d.continuousGreen ^ k).mulVec (fun _ ↦ 1)) := by
  rw [d.integral_pow_measure k hk, d.dotProduct_continuousGreen_pow k, mul_div_assoc]

/-- The generator-inverse moment formula in V2.10, Section 2.3. -/
theorem integral_pow_eq_generator (k : ℕ) (hk : 0 < k) :
    ∫ x, x ^ k ∂d.measure =
      (k.factorial : ℝ) *
        dotProduct d.initial ((((-d.generator)⁻¹) ^ k).mulVec (fun _ ↦ 1)) :=
  d.integral_pow_eq_continuousGreen k hk

end PhaseTypeData

namespace FiniteSubgenerator

variable {s : ℕ} {T : Matrix (Fin s) (Fin s) ℝ}

/-- Uniformization at any valid rate gives the same formula for each positive moment. -/
theorem integral_pow_uniformize (hT : FiniteSubgenerator T) (initial : Fin s → ℝ)
    (hinitial : ∀ i, 0 ≤ initial i) (hmass : ∑ i, initial i ≤ 1) (ν : ℝ)
    (hνpos : 0 < ν) (hνdiag : ∀ i, -T i i ≤ ν) (k : ℕ) (hk : 0 < k) :
    ∫ x, x ^ k ∂(hT.uniformize initial hinitial hmass ν hνpos hνdiag).measure =
      (k.factorial : ℝ) * dotProduct initial (((-T)⁻¹ ^ k).mulVec (fun _ ↦ 1)) := by
  rw [PhaseTypeData.integral_pow_eq_generator _ k hk, hT.generator_uniformize]
  rfl

end FiniteSubgenerator
end SSPRK
