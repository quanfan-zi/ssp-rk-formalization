import SSPRK.PhaseTypeBlockMoments
import SSPRK.PhaseTypePrincipal

/-!
# Vanishing return moments for finite phase-type Green matrices

Positive Green entries form a transitive relation. Consequently a zero immediate return
weight also forces the next Schur return moment to vanish.
-/

open scoped BigOperators

namespace SSPRK

namespace Substochastic

/-- A Green entry is positive exactly when some finite transition power has a positive entry. -/
theorem inv_pos_iff_exists_pow_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : Matrix ι ι ℝ} (hP : Substochastic P) (hinv : (1 - P).det ≠ 0) (i j : ι) :
    0 < ((1 - P)⁻¹) i j ↔ ∃ k : ℕ, 0 < (P ^ k) i j := by
  have hs : HasSum (fun k : ℕ ↦ (P ^ k) i j) (((1 - P)⁻¹) i j) := by
    rw [hP.inv_eq_tsum hinv]
    exact Pi.hasSum.mp (Pi.hasSum.mp (hP.summable_pow hinv).hasSum i) j
  constructor
  · intro hi
    by_contra h
    push Not at h
    have hz : ∀ k : ℕ, (P ^ k) i j = 0 :=
      fun k ↦ le_antisymm (h k) ((hP.pow k).nonneg i j)
    have hzero : ((1 - P)⁻¹) i j = 0 := by
      rw [← hs.tsum_eq]
      simp only [hz, tsum_zero]
    linarith
  · rintro ⟨k, hk⟩
    apply hk.trans_le
    rw [← hs.tsum_eq]
    exact hs.summable.le_tsum k (fun l _ ↦ (hP.pow l).nonneg i j)

/-- Positive Green occupancy is transitive, by concatenating positive finite paths. -/
theorem inv_pos_trans {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : Matrix ι ι ℝ} (hP : Substochastic P) (hinv : (1 - P).det ≠ 0) {i j k : ι}
    (hij : 0 < ((1 - P)⁻¹) i j) (hjk : 0 < ((1 - P)⁻¹) j k) :
    0 < ((1 - P)⁻¹) i k := by
  obtain ⟨a, ha⟩ := (hP.inv_pos_iff_exists_pow_pos hinv i j).mp hij
  obtain ⟨b, hb⟩ := (hP.inv_pos_iff_exists_pow_pos hinv j k).mp hjk
  apply (hP.inv_pos_iff_exists_pow_pos hinv i k).mpr
  refine ⟨a + b, ?_⟩
  rw [pow_add, Matrix.mul_apply]
  exact (mul_pos ha hb).trans_le (Finset.single_le_sum
    (fun l _ ↦ mul_nonneg ((hP.pow a).nonneg i l) ((hP.pow b).nonneg l k))
    (Finset.mem_univ j))

end Substochastic
/-- For a nonnegative matrix with transitive positive support, zero immediate return means
that the next Schur return moment is also zero. -/
theorem phaseBlockEta2_eq_zero_of_eta1_eq_zero {n : ℕ}
    (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hG : ∀ i j, 0 ≤ G i j)
    (htrans : ∀ i j k, 0 < G i j → 0 < G j k → 0 < G i k)
    (heta : phaseBlockEta1 G = 0) : phaseBlockEta2 G = 0 := by
  have hzero : ∀ j : Fin n, G 0 j.succ * G j.succ 0 = 0 := by
    have hs : ∑ j : Fin n, G 0 j.succ * G j.succ 0 = 0 := heta
    intro j
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ ↦ mul_nonneg (hG 0 j.succ) (hG j.succ 0))).mp hs j (Finset.mem_univ j)
  have htriple (i j : Fin n) : G 0 i.succ * G i.succ j.succ * G j.succ 0 = 0 := by
    by_cases hi : G 0 i.succ = 0
    · simp [hi]
    by_cases hij : G i.succ j.succ = 0
    · simp [hij]
    have hp : 0 < G 0 j.succ := htrans 0 i.succ j.succ
      (lt_of_le_of_ne (hG 0 i.succ) (Ne.symm hi))
      (lt_of_le_of_ne (hG i.succ j.succ) (Ne.symm hij))
    have hz := (mul_eq_zero.mp (hzero j)).resolve_left hp.ne'
    rw [hz, mul_zero]
  have hreturn : dotProduct (phaseBlockU G) ((phaseBlockW G).mulVec (phaseBlockV G)) = 0 := by
    simp only [phaseBlockU, phaseBlockV, phaseBlockW, Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    simpa only [mul_assoc] using htriple i j
  rw [phaseBlockEta2, phaseBlock_schur_return, hreturn, heta]
  norm_num

namespace PhaseTypeData

/-- Positive occupancy in a finite phase-type Green matrix is transitive. -/
theorem green_pos_trans {s : ℕ} (d : PhaseTypeData s) {i j k : Fin s}
    (hij : 0 < d.green i j) (hjk : 0 < d.green j k) : 0 < d.green i k :=
  d.substochastic.inv_pos_trans d.transient hij hjk

/-- Any positive scaling of a phase-type Green matrix preserves the zero-return implication. -/
theorem scaled_green_eta2_eq_zero {n : ℕ} (d : PhaseTypeData (n + 1))
    (c : ℝ) (hc : 0 < c) (heta : phaseBlockEta1 (c • d.green) = 0) :
    phaseBlockEta2 (c • d.green) = 0 := by
  apply phaseBlockEta2_eq_zero_of_eta1_eq_zero _ ?_ ?_ heta
  · intro i j
    exact mul_nonneg hc.le (d.substochastic.inv_nonneg d.transient i j)
  · intro i j k hij hjk
    change 0 < c * d.green i j at hij
    change 0 < c * d.green j k at hjk
    change 0 < c * d.green i k
    exact mul_pos hc (d.green_pos_trans
      ((mul_pos_iff_of_pos_left hc).mp hij) ((mul_pos_iff_of_pos_left hc).mp hjk))

/-- A zero first return term in the normalized Green block forces the second term to vanish. -/
theorem normalized_green_eta2_eq_zero {n : ℕ} (d : PhaseTypeData (n + 1))
    (heta : phaseBlockEta1 ((d.green 0 0)⁻¹ • d.green) = 0) :
    phaseBlockEta2 ((d.green 0 0)⁻¹ • d.green) = 0 :=
  d.scaled_green_eta2_eq_zero _ (inv_pos.mpr d.green_zero_zero_pos) heta

end PhaseTypeData
end SSPRK
