import SSPRK.PhaseTypeLawEquality
import SSPRK.PaperMomentBasics

/-!
# Theorem 4.1: the fixed-start Aldous--Shepp bound and process equality

The denominator-free inequality is equivalent to the paper's variance ratio
because a proper PH law started in a transient state has strictly positive mean.
Equality specifies the entire equal-rate sequential generator, including its initial state.
-/

open MeasureTheory ProbabilityTheory

namespace SSPRK.Paper

/-- Theorem 4.1: the minimum variance bound and the Erlang-process characterization. -/
theorem theorem_4_1 {s : ℕ} (hs : 0 < s) (d : PhaseTypeData s) (i : Fin s)
    (hstart : d.initial = Pi.single i 1) :
    (∫ x, x ∂d.measure) ^ 2 / (s : ℝ) ≤ variance (fun x : ℝ ↦ x) d.measure ∧
    (variance (fun x : ℝ ↦ x) d.measure = (∫ x, x ∂d.measure) ^ 2 / (s : ℝ) ↔
      ∃ κ : ℝ, 0 < κ ∧ ∃ e : Fin s ≃ Fin s,
        d.generator.submatrix e e = -κ • chainD s ∧
        ∀ j, d.initial (e j) = if j.val + 1 = s then 1 else 0) := by
  refine ⟨d.variance_lower_bound hs, ?_⟩
  have hmass : d.mass = 1 := by simp [PhaseTypeData.mass, hstart]
  have hmean := d.integral_id_pos_of_mass_one hmass
  constructor
  · intro heq
    obtain ⟨κ, hκ, e, hg, hi⟩ := d.variance_equality_representation hs hmean heq
    refine ⟨κ, hκ, e, hg, ?_⟩
    intro j
    have hj : (j.val + 1 = s) ↔ j = ⟨s - 1, by omega⟩ := by
      simp only [Fin.ext_iff]
      omega
    simpa only [hj] using hi j
  · rintro ⟨κ, hκ, e, hg, hi⟩
    apply (d.variance_eq_iff_erlang hs hmean).mpr
    refine ⟨κ, hκ, ?_⟩
    cases s with
    | zero => omega
    | succ n =>
      have hlast : ∀ j, d.initial (e j) = if j = Fin.last n then 1 else 0 := by
        intro j
        simpa only [Fin.ext_iff, Fin.val_last, Nat.add_right_cancel_iff] using hi j
      simpa only [Nat.cast_add, Nat.cast_one] using
        d.measure_eq_gamma_of_chain κ hκ e hg hlast

end SSPRK.Paper
