import SSPRK.AcyclicMomentBound

/-!
# Theorem 4.4: all adjacent moment ratios of an acyclic PH law

An acyclic representation can be relabelled so that its transient generator is
lower triangular. The natural exponent `k - 1` includes the zeroth moment at `k = 1`.
The equality assertion is for each fixed positive `k`, not only simultaneous equality.
-/

open MeasureTheory ProbabilityTheory

namespace SSPRK.Paper

/-- Theorem 4.4: every positive adjacent moment ratio and its sharp equality case. -/
theorem theorem_4_4 {s : ℕ} (hs : 0 < s) (d : PhaseTypeData s) (hmass : d.mass = 1)
    (hacyclic : ∃ e : Fin s ≃ Fin s, ∀ i j, i < j → d.generator (e i) (e j) = 0)
    (k : ℕ) (hk : 1 ≤ k) :
    ((s : ℝ) + k) / ((s : ℝ) + k - 1) ≤
      (∫ x, x ^ (k - 1) ∂d.measure) * (∫ x, x ^ (k + 1) ∂d.measure) /
        (∫ x, x ^ k ∂d.measure) ^ 2 ∧
    ((∫ x, x ^ (k - 1) ∂d.measure) * (∫ x, x ^ (k + 1) ∂d.measure) /
        (∫ x, x ^ k ∂d.measure) ^ 2 = ((s : ℝ) + k) / ((s : ℝ) + k - 1) ↔
      ∃ κ : ℝ, 0 < κ ∧ d.measure = gammaMeasure (s : ℝ) κ) := by
  obtain ⟨e, he⟩ := hacyclic
  have hd : (d.reindex e).IsLowerAcyclic := by
    intro i j hij
    simpa only [PhaseTypeData.generator_reindex, Matrix.submatrix_apply] using he i j hij
  have hm : (d.reindex e).mass = 1 := by simpa only [PhaseTypeData.mass_reindex] using hmass
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  have h := (d.reindex e).acyclic_moment_ratio hs hd hm n
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
    ← add_assoc, add_sub_cancel_right, PhaseTypeData.measure_reindex] using h

end SSPRK.Paper
