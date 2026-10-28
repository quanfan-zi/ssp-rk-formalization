import SSPRK.PhaseTypeThirdDefectEquality
import SSPRK.PaperMomentBasics

/-!
# Theorem 4.2: the third-moment ratio bound and Erlang equality

The paper assumes an initial probability row on the transient states. The mass-one
hypothesis is essential for the unconditioned Erlang-law conclusion at equality.
The V2.10 defect induction and its equality reduction supply the conclusions.
-/

open MeasureTheory ProbabilityTheory

namespace SSPRK.Paper

/-- Theorem 4.2, with the actual PH probability integrals and both equality directions. -/
theorem theorem_4_2 {s : ℕ} (hs : 0 < s) (d : PhaseTypeData s) (hmass : d.mass = 1) :
    ((s : ℝ) + 2) / ((s : ℝ) + 1) ≤
      (∫ x, x ∂d.measure) * (∫ x, x ^ 3 ∂d.measure) / (∫ x, x ^ 2 ∂d.measure) ^ 2 ∧
    ((∫ x, x ∂d.measure) * (∫ x, x ^ 3 ∂d.measure) / (∫ x, x ^ 2 ∂d.measure) ^ 2 =
        ((s : ℝ) + 2) / ((s : ℝ) + 1) ↔
      ∃ κ : ℝ, 0 < κ ∧ d.measure = gammaMeasure (s : ℝ) κ) := by
  have hmean := d.integral_id_pos_of_mass_one hmass
  refine ⟨d.third_moment_ratio_lower_bound_defect hmean, ?_⟩
  have hsecond := (d.integral_moment_class_defect hmean).second_pos
  have hden : 0 < (s : ℝ) + 1 := by positivity
  have hratio :
      (∫ x, x ∂d.measure) * (∫ x, x ^ 3 ∂d.measure) /
          (∫ x, x ^ 2 ∂d.measure) ^ 2 = ((s : ℝ) + 2) / ((s : ℝ) + 1) ↔
        ((s : ℝ) + 2) * (∫ x, x ^ 2 ∂d.measure) ^ 2 =
          ((s : ℝ) + 1) * (∫ x, x ∂d.measure) * (∫ x, x ^ 3 ∂d.measure) := by
    rw [div_eq_div_iff (ne_of_gt (sq_pos_of_pos hsecond)) (ne_of_gt hden)]
    constructor <;> intro h <;> nlinarith only [h]
  rw [hratio]
  exact d.third_integral_eq_iff_gamma_defect hs hmass hmean

end SSPRK.Paper
