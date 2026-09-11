import SSPRK.PhaseTypeEquality
import SSPRK.PhaseTypeLaw
import SSPRK.PhaseTypeReindex
import SSPRK.ErlangPhaseType
import SSPRK.ErlangVariance

/-!
# Erlang characterization of equality in the PH variance bound

The chain representation theorem and invariance of the probability measure identify
the entire law at equality, not only its first two moments.
-/

open MeasureTheory ProbabilityTheory

namespace SSPRK

/-- The standard Erlang chain has the constant-rate bidiagonal generator. -/
theorem erlangPhaseType_generator (n : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    (erlangPhaseType n κ hκ).generator = -κ • chainD (n + 1) := by
  change κ • (shiftDown (n + 1) - 1) = -κ • (1 - shiftDown (n + 1))
  module

namespace PhaseTypeData

/-- Any representation of the standard chain has its Erlang probability law. -/
theorem measure_eq_gamma_of_chain {n : ℕ} (d : PhaseTypeData (n + 1))
    (κ : ℝ) (hκ : 0 < κ) (e : Fin (n + 1) ≃ Fin (n + 1))
    (hg : d.generator.submatrix e e = -κ • chainD (n + 1))
    (hi : ∀ j, d.initial (e j) = if j = Fin.last n then 1 else 0) :
    d.measure = gammaMeasure (n + 1 : ℝ) κ := by
  have hdata : (d.reindex e).measure = (erlangPhaseType n κ hκ).measure := by
    apply measure_eq_of_initial_generator_eq
    · exact funext hi
    · rw [generator_reindex, erlangPhaseType_generator, hg]
  simpa only [measure_reindex, erlangPhaseType_measure] using hdata

/-- Equality in the PH minimum-variance bound is equivalent to an equal-rate Erlang law. -/
theorem variance_eq_iff_erlang {s : ℕ} (d : PhaseTypeData s) (hs : 0 < s)
    (hmean : 0 < ∫ x, x ∂d.measure) :
    variance (fun x : ℝ ↦ x) d.measure = (∫ x, x ∂d.measure) ^ 2 / (s : ℝ) ↔
      ∃ κ : ℝ, 0 < κ ∧ d.measure = gammaMeasure (s : ℝ) κ := by
  constructor
  · intro heq
    obtain ⟨κ, hκ, e, hg, hi⟩ := d.variance_equality_representation hs hmean heq
    cases s with
    | zero => omega
    | succ n =>
      refine ⟨κ, hκ, ?_⟩
      simpa only [Nat.cast_add, Nat.cast_one] using d.measure_eq_gamma_of_chain κ hκ e hg hi
  · intro hlaw
    obtain ⟨κ, hκ, hμ⟩ := hlaw
    simpa only [hμ] using variance_erlang_eq_mean_sq_div hs hκ

end PhaseTypeData

end SSPRK
