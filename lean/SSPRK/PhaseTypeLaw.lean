import SSPRK.PhaseTypeLaplaceGenerator
import SSPRK.LaplaceUniqueness

/-!
# Independence of the PH law from its uniformizing clock

The initial row and transient generator determine the probability measure. This follows
from the proved integral Laplace formula and uniqueness for nonnegative finite measures.
-/

open MeasureTheory
open scoped BigOperators

namespace SSPRK
namespace PhaseTypeData

/-- Different uniformized data with the same initial row and generator define the same law. -/
theorem measure_eq_of_initial_generator_eq {s : ℕ} (d d' : PhaseTypeData s)
    (hi : d.initial = d'.initial) (hg : d.generator = d'.generator) :
    d.measure = d'.measure := by
  refine Measure.ext_of_laplace_eq_of_ae_nonneg d.ae_nonneg_measure d'.ae_nonneg_measure
    (fun u hu ↦ ?_)
  rw [d.integral_exp_neg_mul_eq_generator u hu, d'.integral_exp_neg_mul_eq_generator u hu]
  simp only [mass, hi, hg]

end PhaseTypeData

namespace FiniteSubgenerator

/-- Any two admissible clock rates give exactly the same PH probability measure. -/
theorem measure_uniformize_eq {s : ℕ} {T : Matrix (Fin s) (Fin s) ℝ}
    (hT : FiniteSubgenerator T) (initial : Fin s → ℝ)
    (hinitial : ∀ i, 0 ≤ initial i) (hmass : ∑ i, initial i ≤ 1) (ν η : ℝ)
    (hνpos : 0 < ν) (hνdiag : ∀ i, -T i i ≤ ν)
    (hηpos : 0 < η) (hηdiag : ∀ i, -T i i ≤ η) :
    (hT.uniformize initial hinitial hmass ν hνpos hνdiag).measure =
      (hT.uniformize initial hinitial hmass η hηpos hηdiag).measure := by
  apply PhaseTypeData.measure_eq_of_initial_generator_eq
  · rfl
  · rw [hT.generator_uniformize, hT.generator_uniformize]

end FiniteSubgenerator
end SSPRK
