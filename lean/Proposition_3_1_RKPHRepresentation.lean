import SSPRK.PaperRKPH
import SSPRK.PaperTransience

/-!
# Proposition 3.1: the RK--PH representation

`AbsolutelyMonotoneAt` contains invertibility and all four inequalities of `(K)_r`.
The normalized initial row is the paper's `pi`; the unnormalized row is `w`.
-/

open scoped BigOperators

namespace SSPRK.Paper

/-- Proposition 3.1, including strict positivity of the normalizing mass. -/
theorem proposition_3_1 {s : ℕ} (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ)
    (r : ℝ) (hr : 0 < r) (h : AbsolutelyMonotoneAt A b r)
    (hord1 : dotProduct b (fun _ ↦ (1 : ℝ)) = 1) :
    (∀ i j, i ≠ j → 0 ≤ (-rkM r A) i j) ∧
    (∀ i, ∑ j, (-rkM r A) i j ≤ 0) ∧
    (-rkM r A).det ≠ 0 ∧
    (∀ i, 0 ≤ rkOmega r b A i) ∧
    0 < rkSigma r b A ∧ rkSigma r b A ≤ 1 ∧
    (h.normalizedPhaseType hr hord1).generator = -rkM r A ∧
    (h.normalizedPhaseType hr hord1).initial = (rkSigma r b A)⁻¹ • rkOmega r b A ∧
    (h.normalizedPhaseType hr hord1).mass = 1 := by
  obtain ⟨hoff, hrow, hdet⟩ := generator_conditions_of_phaseType (h.phaseType hr)
  rw [h.phaseType_generator hr] at hoff hrow hdet
  refine ⟨hoff, hrow, hdet, rkOmega_nonneg r b A hr.le h.output_nonneg, ?_,
    rkSigma_le_one r b A h.output_mass, h.normalizedPhaseType_generator hr hord1,
    h.normalizedPhaseType_initial hr hord1, h.normalizedPhaseType_mass hr hord1⟩
  simpa only [h.phaseType_mass hr] using h.phaseType_mass_pos hr hord1

end SSPRK.Paper
