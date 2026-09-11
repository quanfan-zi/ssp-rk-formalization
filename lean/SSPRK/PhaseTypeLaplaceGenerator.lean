import SSPRK.PhaseTypeLaplace
import SSPRK.PhaseTypeResolvent
import SSPRK.PhaseTypeUniformization

/-!
# Generator formula for the Laplace transform of a PH law

The zero-time mass contributes a constant. The positive-time part is the initial
row paired with the shifted generator inverse and the continuous exit vector.
-/

open MeasureTheory
open scoped BigOperators

namespace SSPRK
namespace PhaseTypeData

variable {s : ℕ} (d : PhaseTypeData s)

/-- The PH Laplace transform in the generator form of Proposition 2.2. -/
theorem integral_exp_neg_mul_eq_generator (u : ℝ) (hu : 0 ≤ u) :
    ∫ x, Real.exp (-u * x) ∂d.measure =
      1 - d.mass + dotProduct d.initial
        ((u • (1 : Matrix (Fin s) (Fin s) ℝ) - d.generator)⁻¹.mulVec
          ((-d.generator).mulVec (fun _ ↦ 1))) := by
  rw [d.integral_exp_neg_mul_measure u hu, d.laplace_resolvent_exit u hu]

end PhaseTypeData

namespace FiniteSubgenerator

variable {s : ℕ} {T : Matrix (Fin s) (Fin s) ℝ}

/-- Every admissible uniformization has the same generator Laplace formula. -/
theorem integral_exp_neg_mul_uniformize (hT : FiniteSubgenerator T) (initial : Fin s → ℝ)
    (hinitial : ∀ i, 0 ≤ initial i) (hmass : ∑ i, initial i ≤ 1) (ν : ℝ)
    (hνpos : 0 < ν) (hνdiag : ∀ i, -T i i ≤ ν) (u : ℝ) (hu : 0 ≤ u) :
    ∫ x, Real.exp (-u * x) ∂(hT.uniformize initial hinitial hmass ν hνpos hνdiag).measure =
      1 - ∑ i, initial i + dotProduct initial
        ((u • (1 : Matrix (Fin s) (Fin s) ℝ) - T)⁻¹.mulVec
          ((-T).mulVec (fun _ ↦ 1))) := by
  rw [PhaseTypeData.integral_exp_neg_mul_eq_generator _ u hu, hT.generator_uniformize]
  rfl

end FiniteSubgenerator
end SSPRK
