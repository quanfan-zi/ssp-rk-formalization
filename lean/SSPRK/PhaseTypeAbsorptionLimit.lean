import SSPRK.PhaseTypeRecordClock
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Passing from finite record clocks to the absorption time

Almost-sure absorption makes bounded Laplace observables eventually equal to their
terminal values. Dominated convergence then passes their expectations to the limit.
-/

open MeasureTheory Filter
open scoped Topology

namespace SSPRK.PhaseTypeData

variable {s : ℕ} (d : PhaseTypeData s)

/-- A nonnegative clock and an observable in `[0,1]` give a bounded Laplace observable. -/
theorem record_laplace_observable_norm_le_one {u : ℝ} (hu : 0 ≤ u)
    (f : Fin (s + 1) → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (n : ℕ) :
    ∀ᵐ records ∂d.canonicalRecords,
      ‖Real.exp (-u * recordClock n records) * f (records n).2‖ ≤ 1 := by
  filter_upwards [d.canonicalRecords_clock_nonneg] with records hclock
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (hf _).1)]
  have he : Real.exp (-u * recordClock n records) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) (hclock n))
  exact (mul_le_mul_of_nonneg_right he (hf _).1).trans (by simpa using (hf (records n).2).2)

/-- On absorbing paths the weighted observable eventually becomes the terminal Laplace kernel. -/
theorem record_laplace_observable_eventually_eq
    (hproper : ∀ᵐ records ∂d.canonicalRecords, firstAbsorptionIndex records ≠ ⊤)
    (u : ℝ) (f : Fin (s + 1) → ℝ) (hfzero : f 0 = 1) :
    ∀ᵐ records ∂d.canonicalRecords, ∀ᶠ n in atTop,
      Real.exp (-u * recordClock n records) * f (records n).2 =
        Real.exp (-u * (recordAbsorptionTime records).toReal) := by
  filter_upwards [d.canonicalRecords_clock_state_eventually_absorbed hproper]
    with records hterminal
  exact hterminal.mono fun n hn ↦ by rw [hn.1, hn.2, hfzero, mul_one]

/-- Bounded Laplace expectations converge to the actual absorption-time expectation. -/
theorem tendsto_integral_record_laplace_observable
    (hproper : ∀ᵐ records ∂d.canonicalRecords, firstAbsorptionIndex records ≠ ⊤)
    {u : ℝ} (hu : 0 ≤ u) (f : Fin (s + 1) → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hfzero : f 0 = 1) :
    Tendsto (fun n ↦ ∫ records,
      Real.exp (-u * recordClock n records) * f (records n).2 ∂d.canonicalRecords)
      atTop (𝓝 (∫ records, Real.exp (-u * (recordAbsorptionTime records).toReal)
        ∂d.canonicalRecords)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ))
  · exact fun n ↦ ((measurable_const.mul (measurable_recordClock n)).exp.mul
      ((measurable_of_countable f).comp (measurable_record_state n))).aestronglyMeasurable
  · exact integrable_const 1
  · exact d.record_laplace_observable_norm_le_one hu f hf
  · filter_upwards [d.record_laplace_observable_eventually_eq hproper u f hfzero]
      with records heq
    exact tendsto_const_nhds.congr' (heq.mono fun n hn ↦ hn.symm)

end SSPRK.PhaseTypeData
