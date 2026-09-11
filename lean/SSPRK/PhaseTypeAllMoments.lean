import SSPRK.PhaseTypeMoments
import SSPRK.PhaseTypeHigherCountMoments

/-!
# All integral moments of finite phase-type laws

Positive integer moments follow from the Erlang mixture and the factorial counting moments.
The zeroth moment of the complete probability law includes the immediate-absorption atom.
-/

open MeasureTheory

namespace SSPRK.PhaseTypeData

variable {s : ℕ} (d : PhaseTypeData s)

/-- Every natural moment of the positive-time mixture has the factorial Green formula. -/
theorem positiveMeasure_pow_moment (k : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ k) d.positiveMeasure ∧
      ∫ x, x ^ k ∂d.positiveMeasure =
        (k.factorial : ℝ) * dotProduct d.initial ((d.green ^ k).mulVec (fun _ ↦ 1)) /
          d.rate ^ k := by
  apply weighted_measure_moment
    (fun n ↦ ProbabilityTheory.gammaMeasure (n + 1) d.rate)
    d.weight (fun n ↦ (n + k).factorial / (n.factorial : ℝ) / d.rate ^ k)
    (fun x ↦ x ^ k) _ d.weight_nonneg
  · intro n
    exact integrable_pow_gammaMeasure (by positivity) d.rate_pos k
  · intro n
    exact (ae_nonneg_gammaMeasure (n + 1) d.rate).mono fun x hx ↦ pow_nonneg hx k
  · intro n
    exact integral_pow_erlangMeasure n k d.rate_pos
  · simpa only [mul_div_assoc] using (d.hasSum_factorial_count_moment k).div_const (d.rate ^ k)

/-- Every positive integer moment of the full absorption law has the factorial Green formula. -/
theorem pow_integral_moment (k : ℕ) (hk : 0 < k) :
    Integrable (fun x : ℝ ↦ x ^ k) d.measure ∧
      ∫ x, x ^ k ∂d.measure =
        (k.factorial : ℝ) * dotProduct d.initial ((d.green ^ k).mulVec (fun _ ↦ 1)) /
          d.rate ^ k := by
  obtain ⟨hint, hmoment⟩ := d.positiveMeasure_pow_moment k
  obtain ⟨hint', heq⟩ := atom_add_measure_moment d.positiveMeasure (1 - d.mass)
    (fun x ↦ x ^ k) hint (zero_pow (Nat.ne_of_gt hk))
  exact ⟨hint', heq.trans hmoment⟩

/-- Every natural power is integrable under a finite phase-type probability law. -/
theorem integrable_pow_measure (k : ℕ) : Integrable (fun x : ℝ ↦ x ^ k) d.measure := by
  cases k with
  | zero => simpa only [pow_zero] using (integrable_const (1 : ℝ))
  | succ k => exact (d.pow_integral_moment (k + 1) (Nat.succ_pos k)).1

/-- The complete-law formula applies to positive powers; the atom at zero contributes nothing. -/
theorem integral_pow_measure (k : ℕ) (hk : 0 < k) :
    ∫ x, x ^ k ∂d.measure =
      (k.factorial : ℝ) * dotProduct d.initial ((d.green ^ k).mulVec (fun _ ↦ 1)) /
        d.rate ^ k :=
  (d.pow_integral_moment k hk).2

/-- The zeroth moment includes the immediate-absorption atom and equals one. -/
@[simp]
theorem integral_pow_zero_measure : ∫ x, x ^ (0 : ℕ) ∂d.measure = 1 := by
  simp

end SSPRK.PhaseTypeData
