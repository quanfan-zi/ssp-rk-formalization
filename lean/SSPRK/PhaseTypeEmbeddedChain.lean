import SSPRK.PhaseTypeQMatrix
import SSPRK.PhaseTypeGenerator
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The embedded jump chain of phase-type data

This file removes the holding probabilities from a phase-type transition matrix.
The resulting substochastic matrix records the transient part of the jump chain
of the associated Q-matrix. Its `PhaseTypeData` wrapper has clock rate one only
to reuse the discrete Green-matrix infrastructure; it does not represent the
same continuous-time law as the original data.
-/

open Filter
open scoped BigOperators Topology

namespace SSPRK
namespace PhaseTypeData

noncomputable section

/-- The transient jump matrix: zero diagonal and normalized off-diagonal rates. -/
def embeddedTransition {s : ℕ} (d : PhaseTypeData s) : Matrix (Fin s) (Fin s) ℝ :=
  fun i j ↦ if i = j then 0 else d.generator i j / (-d.generator i i)

/-- The diagonal matrix of reciprocal transient exit rates. -/
def embeddedHoldingInv {s : ℕ} (d : PhaseTypeData s) : Matrix (Fin s) (Fin s) ℝ :=
  Matrix.diagonal fun i ↦ (-d.generator i i)⁻¹

@[simp]
theorem embeddedTransition_diag {s : ℕ} (d : PhaseTypeData s) (i : Fin s) :
    d.embeddedTransition i i = 0 := by
  simp [embeddedTransition]

theorem embeddedTransition_apply_of_ne {s : ℕ} (d : PhaseTypeData s)
    {i j : Fin s} (hij : i ≠ j) :
    d.embeddedTransition i j = d.generator i j / (-d.generator i i) := by
  simp [embeddedTransition, hij]

/-- Every entry of the transient jump matrix is nonnegative. -/
theorem embeddedTransition_nonneg {s : ℕ} (d : PhaseTypeData s) (i j : Fin s) :
    0 ≤ d.embeddedTransition i j := by
  by_cases hij : i = j
  · simp [embeddedTransition, hij]
  · simp only [embeddedTransition, hij, ↓reduceIte]
    exact div_nonneg (d.generator_nonneg_of_ne hij)
      (neg_nonneg.mpr (d.generator_diag_neg i).le)

private theorem generator_row_sum_nonpos {s : ℕ} (d : PhaseTypeData s) (i : Fin s) :
    ∑ j, d.generator i j ≤ 0 := by
  unfold generator
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.one_apply]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  have hone : (∑ j : Fin s, if i = j then (1 : ℝ) else 0) = 1 := by simp
  rw [hone]
  exact mul_nonpos_of_nonneg_of_nonpos d.rate_pos.le
    (sub_nonpos.mpr (d.substochastic.row_sum_le i))

/-- Each transient jump row has mass at most one; the deficit is absorption. -/
theorem embeddedTransition_row_sum_le {s : ℕ} (d : PhaseTypeData s) (i : Fin s) :
    ∑ j, d.embeddedTransition i j ≤ 1 := by
  have hsplit := Finset.add_sum_erase Finset.univ (d.generator i)
    (Finset.mem_univ i)
  have hoffsum_le : ∑ j ∈ Finset.univ.erase i, d.generator i j ≤ -d.generator i i := by
    linarith [generator_row_sum_nonpos d i]
  calc
    ∑ j, d.embeddedTransition i j =
        ∑ j ∈ Finset.univ.erase i, d.generator i j / (-d.generator i i) := by
      rw [← Finset.sum_erase_add Finset.univ (fun j ↦ d.embeddedTransition i j)
        (Finset.mem_univ i)]
      simp only [embeddedTransition_diag, add_zero]
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [embeddedTransition, Ne.symm hji]
    _ = (∑ j ∈ Finset.univ.erase i, d.generator i j) / (-d.generator i i) := by
      rw [Finset.sum_div]
    _ ≤ 1 := (div_le_one (neg_pos.mpr (d.generator_diag_neg i))).mpr hoffsum_le

/-- The transient jump matrix is substochastic. -/
theorem embeddedTransition_substochastic {s : ℕ} (d : PhaseTypeData s) :
    Substochastic d.embeddedTransition :=
  ⟨d.embeddedTransition_nonneg, d.embeddedTransition_row_sum_le⟩

/-- Factoring the holding rates from the generator gives `I - R`. -/
theorem one_sub_embeddedTransition {s : ℕ} (d : PhaseTypeData s) :
    1 - d.embeddedTransition = d.embeddedHoldingInv * (-d.generator) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.one_apply, embeddedHoldingInv, Matrix.diagonal_mul]
  by_cases hij : i = j
  · subst j
    simp only [embeddedTransition, if_pos, sub_zero, Matrix.neg_apply, inv_neg, neg_mul_neg]
    rw [inv_mul_cancel₀ (d.generator_diag_neg i).ne]
  · simp [embeddedTransition, hij]
    field_simp [ne_of_gt (neg_pos.mpr (d.generator_diag_neg i))]

/-- The reciprocal holding-rate diagonal is nonsingular. -/
theorem embeddedHoldingInv_det_ne_zero {s : ℕ} (d : PhaseTypeData s) :
    d.embeddedHoldingInv.det ≠ 0 := by
  rw [embeddedHoldingInv, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _ ↦
    inv_ne_zero (neg_ne_zero.mpr (d.generator_diag_neg i).ne)

/-- The embedded transient jump chain is transient. -/
theorem one_sub_embeddedTransition_det_ne_zero {s : ℕ} (d : PhaseTypeData s) :
    (1 - d.embeddedTransition).det ≠ 0 := by
  rw [d.one_sub_embeddedTransition, Matrix.det_mul]
  apply mul_ne_zero d.embeddedHoldingInv_det_ne_zero
  rw [d.neg_generator, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ d.rate_pos.ne') d.transient

/-- A rate-one `PhaseTypeData` wrapper for the transient embedded jump chain.

The rate is bookkeeping only; this wrapper is not asserted to have the same
continuous-time law as `d`. -/
def embeddedChain {s : ℕ} (d : PhaseTypeData s) : PhaseTypeData s where
  transition := d.embeddedTransition
  initial := d.initial
  rate := 1
  rate_pos := zero_lt_one
  substochastic := d.embeddedTransition_substochastic
  transient := d.one_sub_embeddedTransition_det_ne_zero
  initial_nonneg := d.initial_nonneg
  initial_mass_le := d.initial_mass_le

@[simp]
theorem embeddedChain_transition {s : ℕ} (d : PhaseTypeData s) :
    d.embeddedChain.transition = d.embeddedTransition := rfl

@[simp]
theorem embeddedChain_initial {s : ℕ} (d : PhaseTypeData s) :
    d.embeddedChain.initial = d.initial := rfl

@[simp]
theorem embeddedChain_rate {s : ℕ} (d : PhaseTypeData s) :
    d.embeddedChain.rate = 1 := rfl

/-- The missing transient row mass is the normalized absorption rate. -/
theorem embeddedChain_exit {s : ℕ} (d : PhaseTypeData s) (i : Fin s) :
    d.embeddedChain.exit i =
      (-d.generator).mulVec (fun _ ↦ 1) i / (-d.generator i i) := by
  change ((1 - d.embeddedTransition).mulVec (fun _ ↦ 1)) i = _
  rw [d.one_sub_embeddedTransition, ← Matrix.mulVec_mulVec]
  simp [embeddedHoldingInv, Matrix.mulVec, div_eq_mul_inv, mul_comm]

/-- Transient embedded-chain entries are the real values of the Q-matrix jump PMF. -/
theorem embeddedTransition_eq_qMatrix_step_toReal {s : ℕ} (d : PhaseTypeData s)
    (i j : Fin s) :
    d.embeddedTransition i j =
      (d.qMatrix.embeddedDTMC.step i.succ j.succ).toReal := by
  by_cases hij : i = j
  · subst j
    rw [d.qMatrix.embeddedDTMC_step_self_of_nonabsorbing
      (d.qMatrix_not_isAbsorbing_succ i)]
    simp [embeddedTransition]
  · rw [d.embeddedDTMC_step_succ_succ hij]
    simp [embeddedTransition, hij, div_nonneg (d.generator_nonneg_of_ne hij)
      (neg_nonneg.mpr (d.generator_diag_neg i).le)]

/-- The embedded-chain exit entry is the Q-matrix jump probability of absorption. -/
theorem embeddedChain_exit_eq_qMatrix_step_toReal {s : ℕ} (d : PhaseTypeData s)
    (i : Fin s) :
    d.embeddedChain.exit i =
      (d.qMatrix.embeddedDTMC.step i.succ 0).toReal := by
  rw [d.embeddedDTMC_step_succ_zero]
  have hnum : 0 ≤ (-d.generator).mulVec (fun _ ↦ 1) i := by
    rw [d.neg_generator_mulVec_one]
    exact mul_nonneg d.rate_pos.le (d.exit_nonneg i)
  have hquot : 0 ≤
      (-d.generator).mulVec (fun _ ↦ 1) i / (-d.generator i i) :=
    div_nonneg hnum (neg_nonneg.mpr (d.generator_diag_neg i).le)
  rw [ENNReal.toReal_ofReal hquot]
  exact d.embeddedChain_exit i

/-- The powers of the transient embedded jump matrix form a summable series. -/
theorem summable_embeddedTransition_pow {s : ℕ} (d : PhaseTypeData s) :
    Summable (fun n : ℕ ↦ d.embeddedTransition ^ n) :=
  d.embeddedTransition_substochastic.summable_pow
    d.one_sub_embeddedTransition_det_ne_zero

/-- Transient jump probabilities vanish as the number of jumps tends to infinity. -/
theorem embeddedTransition_pow_tendsto_zero {s : ℕ} (d : PhaseTypeData s) :
    Tendsto (fun n : ℕ ↦ d.embeddedTransition ^ n) atTop (𝓝 0) :=
  d.summable_embeddedTransition_pow.tendsto_atTop_zero

/-- The embedded-chain Green matrix is the Neumann sum of transient jump powers. -/
theorem embeddedChain_green_eq_tsum {s : ℕ} (d : PhaseTypeData s) :
    d.embeddedChain.green = ∑' n : ℕ, d.embeddedTransition ^ n := by
  simpa only [embeddedChain, green] using
    d.embeddedTransition_substochastic.inv_eq_tsum
      d.one_sub_embeddedTransition_det_ne_zero

end

end PhaseTypeData
end SSPRK
