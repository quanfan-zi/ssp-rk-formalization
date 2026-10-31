import SSPRK.PhaseTypeUniformization

/-!
# A determinant-free transience criterion

Survival in the uniformized finite transient block is the row sum of its powers.
This file proves that decay of all survival probabilities forces nonsingularity;
the converse reuses the established substochastic Neumann series.
-/

open Filter
open scoped BigOperators Topology

namespace SSPRK

namespace Substochastic

/-- Vanishing survival probabilities imply entrywise decay of every transition power. -/
theorem tendsto_pow_zero_of_survival {s : ℕ} {P : Matrix (Fin s) (Fin s) ℝ}
    (hP : Substochastic P)
    (hsurvival : ∀ i, Tendsto (fun n : ℕ ↦ ∑ j, (P ^ n) i j) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ P ^ n) atTop (𝓝 0) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact squeeze_zero (fun n ↦ (hP.pow n).nonneg i j)
    (fun n ↦ Finset.single_le_sum (fun k _ ↦ (hP.pow n).nonneg i k)
      (Finset.mem_univ j)) (hsurvival i)

/-- A transient substochastic block is nonsingular, without assuming an inverse in advance. -/
theorem det_one_sub_ne_zero_of_survival {s : ℕ} {P : Matrix (Fin s) (Fin s) ℝ}
    (hP : Substochastic P)
    (hsurvival : ∀ i, Tendsto (fun n : ℕ ↦ ∑ j, (P ^ n) i j) atTop (𝓝 0)) :
    (1 - P).det ≠ 0 := by
  intro hdet
  have hzero (n : ℕ) : (1 - P ^ n).det = 0 := by
    rw [← mul_neg_geom_sum P n, Matrix.det_mul, hdet, zero_mul]
  have hpow := hP.tendsto_pow_zero_of_survival hsurvival
  have hlim : Tendsto (fun n : ℕ ↦ (1 - P ^ n).det) atTop (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero, id_eq, Matrix.det_one, Function.comp_def] using
      (continuous_id.matrix_det.tendsto ((1 : Matrix (Fin s) (Fin s) ℝ) - 0)).comp
        (tendsto_const_nhds.sub hpow)
  exact one_ne_zero (tendsto_nhds_unique hlim (by
    simpa only [hzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))))

/-- Nonsingularity makes every uniformized survival probability vanish. -/
theorem survival_tendsto_zero {s : ℕ} {P : Matrix (Fin s) (Fin s) ℝ}
    (hP : Substochastic P) (hdet : (1 - P).det ≠ 0) (i : Fin s) :
    Tendsto (fun n : ℕ ↦ ∑ j, (P ^ n) i j) atTop (𝓝 0) := by
  have hpow := (hP.summable_pow hdet).tendsto_atTop_zero
  simpa only [Matrix.zero_apply, Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun j _ ↦
      tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hpow i) j)

end Substochastic

/-- A finite generator is transient when one positive uniformizing clock gives a
substochastic block whose survival probabilities vanish from every initial state.
This definition does not assume a determinant or an inverse. -/
def HasTransientUniformization {s : ℕ} (T : Matrix (Fin s) (Fin s) ℝ) : Prop :=
  ∃ ν : ℝ, 0 < ν ∧ Substochastic (FiniteSubgenerator.transition (T := T) ν) ∧
    ∀ i, Tendsto (fun n : ℕ ↦ ∑ j,
      (FiniteSubgenerator.transition (T := T) ν ^ n) i j) atTop (𝓝 0)

/-- The transient-generator criterion, with the necessity proved from survival decay. -/
theorem hasTransientUniformization_iff {s : ℕ} (T : Matrix (Fin s) (Fin s) ℝ) :
    HasTransientUniformization T ↔
      (∀ i j, i ≠ j → 0 ≤ T i j) ∧ (∀ i, ∑ j, T i j ≤ 0) ∧ T.det ≠ 0 := by
  constructor
  · rintro ⟨ν, hν, hP, hsurvival⟩
    have hgen : T = ν • (FiniteSubgenerator.transition (T := T) ν - 1) := by
      rw [FiniteSubgenerator.transition, add_sub_cancel_left, smul_smul,
        mul_inv_cancel₀ hν.ne', one_smul]
    have hdet := hP.det_one_sub_ne_zero_of_survival hsurvival
    refine ⟨?_, ?_, ?_⟩
    · rw [hgen]
      intro i j hij
      simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply,
        Matrix.one_apply, if_neg hij, sub_zero] using mul_nonneg hν.le (hP.nonneg i j)
    · rw [hgen]
      intro i
      simpa [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, ← Finset.mul_sum,
        Finset.sum_sub_distrib, Matrix.one_apply] using
        mul_nonpos_of_nonneg_of_nonpos hν.le (sub_nonpos.mpr (hP.row_sum_le i))
    · rw [FiniteSubgenerator.one_sub_transition, Matrix.det_smul, Matrix.det_neg] at hdet
      exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hdet).2).2
  · rintro ⟨hoff, hrow, hdet⟩
    let hT : FiniteSubgenerator T := ⟨hoff, hrow, by simpa [Matrix.det_neg] using hdet⟩
    refine ⟨FiniteSubgenerator.canonicalRate (T := T),
      FiniteSubgenerator.canonicalRate_pos, ?_, ?_⟩
    · exact hT.transition_substochastic FiniteSubgenerator.canonicalRate_pos
        FiniteSubgenerator.le_canonicalRate_neg_diag
    · exact (hT.transition_substochastic FiniteSubgenerator.canonicalRate_pos
        FiniteSubgenerator.le_canonicalRate_neg_diag).survival_tendsto_zero
          (hT.transition_transient FiniteSubgenerator.canonicalRate_pos)

end SSPRK
