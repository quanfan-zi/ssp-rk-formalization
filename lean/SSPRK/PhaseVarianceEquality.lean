import SSPRK.PhaseVariance

/-!
# Energy equality for the phase-variance bound

Equality at an initial state forces every energy defect on its positively occupied states
to vanish, including both absorption and transition defects.
-/

open scoped BigOperators

namespace SSPRK

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The nonnegative local defect in the phase-variance energy estimate. -/
def phaseEnergyDefect (P : Matrix ι ι ℝ) (m f : ι → ℝ) (j : ι) : ℝ :=
  (1 - ∑ k, P j k) * (m j ^ 2 - f j) +
    ∑ k, P j k * ((m j - m k) ^ 2 - (f j - f k))

omit [DecidableEq ι] in
/-- Potential upper and increment bounds make every local energy defect nonnegative. -/
lemma phaseEnergyDefect_nonneg (P : Matrix ι ι ℝ) (m f : ι → ℝ)
    (hP : Substochastic P) (hupper : ∀ j, f j ≤ m j ^ 2)
    (hdiff : ∀ j k, f j - f k ≤ (m j - m k) ^ 2) (j : ι) :
    0 ≤ phaseEnergyDefect P m f j := by
  exact add_nonneg
    (mul_nonneg (sub_nonneg.mpr (hP.row_sum_le j)) (sub_nonneg.mpr (hupper j)))
    (Finset.sum_nonneg fun k _ ↦ mul_nonneg (hP.nonneg j k) (sub_nonneg.mpr (hdiff j k)))

/-- The local energy defect equals the residual in the variance Poisson equation. -/
lemma phaseEnergyDefect_eq (P : Matrix ι ι ℝ) (m f : ι → ℝ)
    (hm : (1 - P).mulVec m = fun _ ↦ 1) :
    phaseEnergyDefect P m f =
      (2 : ℝ) • m - (1 - P).mulVec (fun j ↦ m j ^ 2 + f j) := by
  funext j
  have hrow : ∑ k, P j k * m k = m j - 1 := by
    have hj := congrFun hm j
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hj
    change m j - ∑ k, P j k * m k = 1 at hj
    linarith
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  change (1 - ∑ k, P j k) * (m j ^ 2 - f j) +
      ∑ k, P j k * ((m j - m k) ^ 2 - (f j - f k)) =
    2 * m j - ((m j ^ 2 + f j) - ∑ k, P j k * (m k ^ 2 + f k))
  have hexpand :
      ∑ k, P j k * ((m j - m k) ^ 2 - (f j - f k)) =
        (∑ k, P j k) * (m j ^ 2 - f j) - 2 * m j * (∑ k, P j k * m k) +
          ∑ k, P j k * (m k ^ 2 + f k) := by
    simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hexpand, hrow]
  ring

/-- Green occupation averages the local energy defects to the global variance residual. -/
lemma mulVec_phaseEnergyDefect (P N : Matrix ι ι ℝ) (m f : ι → ℝ)
    (hm : (1 - P).mulVec m = fun _ ↦ 1) (hright : N * (1 - P) = 1) :
    N.mulVec (phaseEnergyDefect P m f) =
      (2 : ℝ) • N.mulVec m - (fun j ↦ m j ^ 2 + f j) := by
  rw [phaseEnergyDefect_eq P m f hm, Matrix.mulVec_sub, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, hright, Matrix.one_mulVec]

omit [DecidableEq ι] in
/-- A vanishing local defect forces every positively weighted energy bound to be an equality. -/
lemma phaseEnergyDefect_eq_zero_iff (P : Matrix ι ι ℝ) (m f : ι → ℝ)
    (hP : Substochastic P) (hupper : ∀ j, f j ≤ m j ^ 2)
    (hdiff : ∀ j k, f j - f k ≤ (m j - m k) ^ 2) (j : ι) :
    phaseEnergyDefect P m f j = 0 ↔
      (0 < 1 - ∑ k, P j k → f j = m j ^ 2) ∧
        (∀ k, 0 < P j k → f j - f k = (m j - m k) ^ 2) := by
  have ha : 0 ≤ (1 - ∑ k, P j k) * (m j ^ 2 - f j) :=
    mul_nonneg (sub_nonneg.mpr (hP.row_sum_le j)) (sub_nonneg.mpr (hupper j))
  have ht : ∀ k, 0 ≤ P j k * ((m j - m k) ^ 2 - (f j - f k)) :=
    fun k ↦ mul_nonneg (hP.nonneg j k) (sub_nonneg.mpr (hdiff j k))
  have hs : 0 ≤ ∑ k, P j k * ((m j - m k) ^ 2 - (f j - f k)) :=
    Finset.sum_nonneg fun k _ ↦ ht k
  constructor
  · intro hzero
    obtain ⟨habs, hsum⟩ := (add_eq_zero_iff_of_nonneg ha hs).mp hzero
    constructor
    · intro hj
      have hz := (mul_eq_zero.mp habs).resolve_left hj.ne'
      linarith
    · intro k hk
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ ↦ ht l)).mp hsum k
        (Finset.mem_univ k)
      have hzero := (mul_eq_zero.mp hz).resolve_left hk.ne'
      linarith
  · rintro ⟨habs, hjump⟩
    apply (add_eq_zero_iff_of_nonneg ha hs).mpr
    constructor
    · rcases eq_or_lt_of_le (sub_nonneg.mpr (hP.row_sum_le j)) with hj | hj
      · rw [← hj, zero_mul]
      · rw [habs hj, sub_self, mul_zero]
    · apply Finset.sum_eq_zero
      intro k _
      rcases eq_or_lt_of_le (hP.nonneg j k) with hk | hk
      · rw [← hk, zero_mul]
      · rw [hjump k hk, sub_self, mul_zero]

/-- Equality in the pointwise variance bound annihilates all positively occupied defects. -/
theorem phase_variance_defect_equality (P N : Matrix ι ι ℝ) (m f : ι → ℝ) (q : ℝ)
    (hP : Substochastic P) (hN : ∀ i j, 0 ≤ N i j) (hq : 0 < q)
    (hm : (1 - P).mulVec m = fun _ ↦ 1) (hright : N * (1 - P) = 1)
    (hupper : ∀ j, f j ≤ m j ^ 2)
    (hdiff : ∀ j k, f j - f k ≤ (m j - m k) ^ 2)
    (i : ι) (hlower : m i ^ 2 ≤ q * f i)
    (heq : (q + 1) * m i ^ 2 = 2 * q * N.mulVec m i) :
    m i ^ 2 = q * f i ∧ ∀ j, 0 < N i j → phaseEnergyDefect P m f j = 0 := by
  have hd : ∀ j, 0 ≤ phaseEnergyDefect P m f j :=
    phaseEnergyDefect_nonneg P m f hP hupper hdiff
  have hn : 0 ≤ N.mulVec (phaseEnergyDefect P m f) i := by
    change 0 ≤ ∑ j, N i j * phaseEnergyDefect P m f j
    exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (hN i j) (hd j)
  have hid : N.mulVec (phaseEnergyDefect P m f) i =
      2 * N.mulVec m i - (m i ^ 2 + f i) := by
    exact congrFun (mulVec_phaseEnergyDefect P N m f hm hright) i
  have hnzero : N.mulVec (phaseEnergyDefect P m f) i = 0 := by
    nlinarith
  refine ⟨by nlinarith, ?_⟩
  intro j hj
  change ∑ k, N i k * phaseEnergyDefect P m f k = 0 at hnzero
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ ↦ mul_nonneg (hN i k) (hd k))).mp hnzero j (Finset.mem_univ j)
  exact (mul_eq_zero.mp hz).resolve_left hj.ne'

/-- Equality in the pointwise phase bound forces potential, absorption and jump equalities
on every state with positive Green occupation from the initial state. -/
theorem phase_variance_equality_of_potential (P N : Matrix ι ι ℝ) (f : ι → ℝ) (q : ℝ)
    (hP : Substochastic P) (hN : ∀ i j, 0 ≤ N i j) (hq : 0 < q)
    (hleft : (1 - P) * N = 1) (hright : N * (1 - P) = 1)
    (hlower : ∀ j, (N.mulVec (fun _ ↦ (1 : ℝ)) j) ^ 2 ≤ q * f j)
    (hupper : ∀ j, f j ≤ (N.mulVec (fun _ ↦ (1 : ℝ)) j) ^ 2)
    (hdiff : ∀ j k, f j - f k ≤
      (N.mulVec (fun _ ↦ (1 : ℝ)) j - N.mulVec (fun _ ↦ (1 : ℝ)) k) ^ 2)
    (i : ι)
    (heq : (q + 1) * (N.mulVec (fun _ ↦ (1 : ℝ)) i) ^ 2 =
      2 * q * N.mulVec (N.mulVec (fun _ ↦ (1 : ℝ))) i) :
    (N.mulVec (fun _ ↦ (1 : ℝ)) i) ^ 2 = q * f i ∧
      ∀ j, 0 < N i j →
        (0 < 1 - ∑ k, P j k → f j = (N.mulVec (fun _ ↦ (1 : ℝ)) j) ^ 2) ∧
          ∀ k, 0 < P j k → f j - f k =
            (N.mulVec (fun _ ↦ (1 : ℝ)) j - N.mulVec (fun _ ↦ (1 : ℝ)) k) ^ 2 := by
  let m := N.mulVec (fun _ ↦ (1 : ℝ))
  have hm : (1 - P).mulVec m = fun _ ↦ 1 := by
    rw [show m = N.mulVec (fun _ ↦ (1 : ℝ)) from rfl,
      Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
  obtain ⟨hbase, hoccupied⟩ := phase_variance_defect_equality P N m f q hP hN hq
    hm hright hupper hdiff i (hlower i) heq
  refine ⟨hbase, ?_⟩
  intro j hj
  exact (phaseEnergyDefect_eq_zero_iff P m f hP hupper hdiff j).mp (hoccupied j hj)

end SSPRK
