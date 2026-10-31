import SSPRK.PaperTransience
import SSPRK.SubgeneratorTransience

/-!
# Proposition 2.3: the transient subintensity criterion

Transience is expressed by vanishing survival probabilities under a positive
uniformizing clock. This condition does not presuppose matrix invertibility.
The companion theorem constructs the canonical CTMC for every initial row and
includes almost-sure finite absorption.
-/

open MeasureTheory Filter
open scoped BigOperators Topology

namespace SSPRK.Paper

/-- Proposition 2.3: precisely the nonsingular subintensity matrices generate transient PH laws. -/
theorem proposition_2_3 {s : ℕ} (T : Matrix (Fin s) (Fin s) ℝ) :
    (∃ ν : ℝ, 0 < ν ∧ Substochastic (1 + ν⁻¹ • T) ∧
      ∀ i, Tendsto (fun n : ℕ ↦ ∑ j, ((1 + ν⁻¹ • T) ^ n) i j) atTop (𝓝 0)) ↔
      (∀ i j, i ≠ j → 0 ≤ T i j) ∧ (∀ i, ∑ j, T i j ≤ 0) ∧ T.det ≠ 0 :=
  hasTransientUniformization_iff T

/-- The same criterion constructs an actual almost-surely absorbing canonical CTMC. -/
theorem proposition_2_3_canonical_absorption {s : ℕ} (T : Matrix (Fin s) (Fin s) ℝ) :
    (∀ α : Fin s → ℝ, (∀ i, 0 ≤ α i) → (∑ i, α i ≤ 1) →
      ∃ d : PhaseTypeData s, d.generator = T ∧ d.initial = α ∧
        (∀ᵐ records ∂d.canonicalRecords,
          PhaseTypeData.recordAbsorptionTime records ≠ ⊤)) ↔
      (∀ i j, i ≠ j → 0 ≤ T i j) ∧ (∀ i, ∑ j, T i j ≤ 0) ∧ T.det ≠ 0 := by
  constructor
  · intro h
    obtain ⟨d, hd, _, _⟩ := h (fun _ ↦ 0) (fun _ ↦ le_rfl) (by simp)
    simpa only [hd] using generator_conditions_of_phaseType d
  · rintro ⟨hoff, hrow, hdet⟩ α hα hmass
    exact exists_absorbing_phaseType_of_generator_conditions T hoff hrow hdet α hα hmass

end SSPRK.Paper
