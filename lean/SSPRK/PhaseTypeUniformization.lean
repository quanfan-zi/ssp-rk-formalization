import SSPRK.PhaseTypeData

/-!
# Uniformization of finite phase-type generators

A finite subgenerator with nonnegative off-diagonal entries and nonpositive row sums has a
uniformized discrete representation at every positive rate dominating its negative diagonal.
-/

open scoped BigOperators

namespace SSPRK

/-- A finite transient generator before choosing a uniformizing clock rate. -/
structure FiniteSubgenerator {s : ℕ} (T : Matrix (Fin s) (Fin s) ℝ) : Prop where
  offdiag_nonneg : ∀ i j, i ≠ j → 0 ≤ T i j
  row_sum_nonpos : ∀ i, ∑ j, T i j ≤ 0
  det_neg_ne_zero : (-T).det ≠ 0

namespace FiniteSubgenerator

variable {s : ℕ} {T : Matrix (Fin s) (Fin s) ℝ}

/-- The transition matrix obtained from `T` at clock rate `ν`. -/
noncomputable def transition (ν : ℝ) : Matrix (Fin s) (Fin s) ℝ := 1 + ν⁻¹ • T

/-- The canonical finite uniformizing rate, which strictly dominates every negative diagonal. -/
noncomputable def canonicalRate : ℝ := 1 + ∑ i, |T i i|

theorem canonicalRate_pos : 0 < canonicalRate (T := T) := by
  unfold canonicalRate
  positivity

theorem le_canonicalRate_neg_diag (i : Fin s) : -T i i ≤ canonicalRate (T := T) := by
  unfold canonicalRate
  calc
    -T i i ≤ |T i i| := neg_le_abs _
    _ ≤ ∑ j, |T j j| :=
      Finset.single_le_sum (f := fun j ↦ |T j j|) (fun j _ ↦ abs_nonneg _) (Finset.mem_univ i)
    _ ≤ 1 + ∑ j, |T j j| := le_add_of_nonneg_left zero_le_one

theorem transition_substochastic (hT : FiniteSubgenerator T) {ν : ℝ} (hνpos : 0 < ν)
    (hνdiag : ∀ i, -T i i ≤ ν) : Substochastic (transition (T := T) ν) := by
  constructor
  · intro i j
    by_cases hij : i = j
    · subst j
      unfold transition
      simp only [Matrix.add_apply, Matrix.one_apply, if_pos]
      change 0 ≤ 1 + ν⁻¹ * T i i
      have hinv : 0 < ν⁻¹ := inv_pos.mpr hνpos
      have hsum : 0 ≤ ν + T i i := by linarith [hνdiag i]
      have hmul : 0 ≤ ν⁻¹ * (ν + T i i) := mul_nonneg (le_of_lt hinv) hsum
      convert hmul using 1; field_simp
    · change 0 ≤ (if i = j then 1 else 0) + ν⁻¹ * T i j
      rw [if_neg hij, zero_add]
      exact mul_nonneg (le_of_lt (inv_pos.mpr hνpos)) (hT.offdiag_nonneg i j hij)
  · intro i
    calc
      ∑ j, transition (T := T) ν i j = 1 + ν⁻¹ * ∑ j, T i j := by
        unfold transition
        simp only [Matrix.add_apply, Matrix.one_apply]
        rw [Finset.sum_add_distrib]
        change (∑ x, (if i = x then 1 else 0)) + ∑ x, ν⁻¹ * T i x = 1 + ν⁻¹ * ∑ j, T i j
        have hone : (∑ x : Fin s, if i = x then (1 : ℝ) else 0) = 1 := by simp
        rw [hone]
        rw [← Finset.mul_sum]
      _ ≤ 1 := by
        have hnonpos : ν⁻¹ * ∑ j, T i j ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt (inv_pos.mpr hνpos)) (hT.row_sum_nonpos i)
        linarith

theorem one_sub_transition (ν : ℝ) : 1 - transition (T := T) ν = ν⁻¹ • (-T) := by
  rw [transition, sub_add_eq_sub_sub, sub_self, zero_sub, smul_neg]

theorem transition_transient (hT : FiniteSubgenerator T) {ν : ℝ} (hνpos : 0 < ν) :
    (1 - transition (T := T) ν).det ≠ 0 := by
  rw [one_sub_transition, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (ne_of_gt (inv_pos.mpr hνpos))) hT.det_neg_ne_zero

/-- Build `PhaseTypeData` from a finite subgenerator and a chosen valid uniformizing rate. -/
noncomputable def uniformize (hT : FiniteSubgenerator T) (initial : Fin s → ℝ)
    (initial_nonneg : ∀ i, 0 ≤ initial i) (initial_mass_le : ∑ i, initial i ≤ 1) (ν : ℝ)
    (hνpos : 0 < ν) (hνdiag : ∀ i, -T i i ≤ ν) : PhaseTypeData s where
  transition := transition (T := T) ν
  initial := initial
  rate := ν
  rate_pos := hνpos
  substochastic := transition_substochastic hT hνpos hνdiag
  transient := transition_transient hT hνpos
  initial_nonneg := initial_nonneg
  initial_mass_le := initial_mass_le

theorem generator_uniformize (hT : FiniteSubgenerator T) (initial : Fin s → ℝ)
    (initial_nonneg : ∀ i, 0 ≤ initial i) (initial_mass_le : ∑ i, initial i ≤ 1) (ν : ℝ)
    (hνpos : 0 < ν) (hνdiag : ∀ i, -T i i ≤ ν) :
    (uniformize hT initial initial_nonneg initial_mass_le ν hνpos hνdiag).generator = T := by
  change ν • (transition (T := T) ν - 1) = T
  rw [transition, add_sub_cancel_left, smul_smul]
  rw [mul_inv_cancel₀ (ne_of_gt hνpos), one_smul]

/-- Build a uniformized phase-type representation using the explicit canonical clock rate. -/
noncomputable def uniformizeCanonical (hT : FiniteSubgenerator T) (initial : Fin s → ℝ)
    (initial_nonneg : ∀ i, 0 ≤ initial i) (initial_mass_le : ∑ i, initial i ≤ 1) :
    PhaseTypeData s :=
  uniformize hT initial initial_nonneg initial_mass_le (canonicalRate (T := T))
    (canonicalRate_pos (T := T)) (le_canonicalRate_neg_diag (T := T))

theorem generator_uniformizeCanonical (hT : FiniteSubgenerator T) (initial : Fin s → ℝ)
    (initial_nonneg : ∀ i, 0 ≤ initial i) (initial_mass_le : ∑ i, initial i ≤ 1) :
    (uniformizeCanonical hT initial initial_nonneg initial_mass_le).generator = T := by
  apply generator_uniformize hT initial initial_nonneg initial_mass_le

end FiniteSubgenerator
end SSPRK
