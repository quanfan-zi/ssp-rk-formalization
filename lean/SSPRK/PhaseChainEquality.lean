import SSPRK.PhaseVarianceEquality
import SSPRK.VariancePotentialEquality
import SSPRK.ChainMatrices
import SSPRK.VariancePotentialLevels
import SSPRK.GreenReachability
import SSPRK.PhaseChainRow

/-!
# Chain rigidity from pointwise phase-variance equality

The equality potential orders all mean lifetimes into equally spaced levels. Its energy
equalities then restrict transitions on every state reached from the equality state.
-/

open scoped BigOperators

namespace SSPRK

/-- The Green row sums are positive because their substochastic balance contains a unit source. -/
lemma green_mean_pos {s : ℕ} (P N : Matrix (Fin s) (Fin s) ℝ)
    (hP : Substochastic P) (hN : ∀ i j, 0 ≤ N i j) (hleft : (1 - P) * N = 1)
    (i : Fin s) : 0 < N.mulVec (fun _ ↦ (1 : ℝ)) i := by
  let m := N.mulVec (fun _ ↦ (1 : ℝ))
  have hm : ∀ j, 0 ≤ m j := by
    intro j
    change 0 ≤ ∑ k, N j k * 1
    exact Finset.sum_nonneg fun k _ ↦ mul_nonneg (hN j k) zero_le_one
  have hbalance : (1 - P).mulVec m = fun _ ↦ 1 := by
    rw [show m = N.mulVec (fun _ ↦ (1 : ℝ)) from rfl,
      Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
  have hi := congrFun hbalance i
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hi
  have hsum : 0 ≤ P.mulVec m i := by
    change 0 ≤ ∑ j, P i j * m j
    exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (hP.nonneg i j) (hm j)
  change m i - P.mulVec m i = 1 at hi
  change 0 < m i
  linarith

/-- Pointwise equality gives equally spaced levels and local chain restrictions on occupied rows. -/
theorem phase_variance_chain_certificate {n : ℕ}
    (P N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hP : Substochastic P) (hN : ∀ i j, 0 ≤ N i j)
    (hleft : (1 - P) * N = 1) (hright : N * (1 - P) = 1)
    (i : Fin (n + 1))
    (heq : ((n + 1 : ℝ) + 1) * (N.mulVec (fun _ ↦ (1 : ℝ)) i) ^ 2 =
      2 * (n + 1 : ℝ) * N.mulVec (N.mulVec (fun _ ↦ (1 : ℝ))) i) :
    ∃ a : ℝ, 0 < a ∧ ∃ e : Fin (n + 1) ≃ Fin (n + 1),
      e (Fin.last n) = i ∧
      (∀ k, N.mulVec (fun _ ↦ (1 : ℝ)) (e k) = (k.val + 1 : ℝ) * a) ∧
      ∀ j, 0 < N i (e j) →
        (0 < 1 - ∑ k, P (e j) k → j.val = 0) ∧
          ∀ k, 0 < P (e j) (e k) → j = k ∨ j.val = k.val + 1 := by
  let m := N.mulVec (fun _ ↦ (1 : ℝ))
  have hm : ∀ j, 0 < m j := green_mean_pos P N hP hN hleft
  obtain ⟨f, _, hlower, hupper, hdiff, hclass⟩ :=
    exists_variance_potential_with_equality (n + 1) m (fun j ↦ (hm j).le)
  have hbound : m i ^ 2 = (n + 1 : ℝ) * f i ∧
      ∀ j, 0 < N i j →
        (0 < 1 - ∑ k, P j k → f j = m j ^ 2) ∧
          ∀ k, 0 < P j k → f j - f k = (m j - m k) ^ 2 :=
    phase_variance_equality_of_potential P N f (n + 1) hP hN (by positivity)
      hleft hright (by simpa only [Nat.cast_add, Nat.cast_one] using hlower)
      hupper hdiff i heq
  obtain ⟨e, he⟩ := hclass i (hm i) (by simpa only [Nat.cast_add, Nat.cast_one] using hbound.1)
  let a := m i / (n + 1 : ℝ)
  have ha : 0 < a := div_pos (hm i) (by positivity)
  have hlevels : ∀ k, m (e k) = (k.val + 1 : ℝ) * a := by
    intro k
    simpa only [Nat.cast_add, Nat.cast_one, mul_div_assoc] using he k
  have htotal : m i = (n + 1 : ℝ) * a := by
    dsimp only [a]
    field_simp
  have htop : e (Fin.last n) = i := by
    have hindex := hlevels (e.symm i)
    rw [e.apply_symm_apply] at hindex
    have hv : ((e.symm i).val : ℝ) = n := by nlinarith
    have hi : e.symm i = Fin.last n := Fin.ext (by exact_mod_cast hv)
    exact (congrArg e hi).symm.trans (e.apply_symm_apply i)
  have hftop : f (e (Fin.last n)) = (n + 1 : ℝ) * a ^ 2 := by
    rw [htop]
    apply mul_left_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0)
    have hb := hbound.1
    rw [htotal] at hb
    nlinarith only [hb]
  have hflevels := variance_potential_permuted_levels m f e hlevels hupper hdiff hftop
  refine ⟨a, ha, e, htop, hlevels, ?_⟩
  intro j hj
  have henergy := hbound.2 (e j) hj
  constructor
  · intro habs
    exact variance_potential_level_absorb_eq ha m f e hlevels hflevels j (henergy.1 habs)
  · intro k hk
    exact variance_potential_level_jump_eq ha m f e hlevels hflevels j k (henergy.2 (e k) hk)

/-- A permuted constant-rate descending chain has the scaled cumulative Green matrix. -/
theorem green_eq_chain_of_transition {s : ℕ} (P N : Matrix (Fin s) (Fin s) ℝ)
    (e : Fin s ≃ Fin s) (a : ℝ) (ha : a ≠ 0) (hright : N * (1 - P) = 1)
    (hform : P.submatrix e e = 1 - a⁻¹ • chainD s) :
    N.submatrix e e = a • chainL s := by
  have hNC : N.submatrix e e * (a⁻¹ • chainD s) = 1 := by
    have h := congrArg (fun M : Matrix (Fin s) (Fin s) ℝ ↦ M.submatrix e e) hright
    dsimp only at h
    rw [← Matrix.submatrix_mul_equiv _ _ e e e] at h
    simp only [Matrix.submatrix_sub, Pi.sub_apply, Matrix.submatrix_one_equiv] at h
    rw [hform, sub_sub_cancel] at h
    exact h
  have hCL : (a⁻¹ • chainD s) * (a • chainL s) = 1 := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ha,
      one_smul, chainD_mul_chainL]
  calc
    N.submatrix e e = N.submatrix e e * ((a⁻¹ • chainD s) * (a • chainL s)) := by
      rw [hCL, Matrix.mul_one]
    _ = (N.submatrix e e * (a⁻¹ • chainD s)) * (a • chainL s) := (Matrix.mul_assoc ..).symm
    _ = a • chainL s := by rw [hNC, Matrix.one_mul]

/-- Positive predecessor transitions propagate occupation from the top level to every state. -/
lemma chain_all_occupied {n : ℕ} (P N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hN : ∀ i j, 0 ≤ N i j)
    (hright : N * (1 - P) = 1) (e : Fin (n + 1) ≃ Fin (n + 1))
    (i : Fin (n + 1)) (htop : e (Fin.last n) = i)
    (hdown : ∀ j : Fin n, 0 < N i (e j.succ) → 0 < P (e j.succ) (e j.castSucc)) :
    ∀ k, 0 < N i (e k) := by
  intro k
  induction k using Fin.reverseInduction with
  | last =>
    rw [htop]
    exact lt_of_lt_of_le zero_lt_one (one_le_green_diag_of_mul_one_sub hP hN hright i)
  | cast j ih =>
    exact green_pos_of_pos_of_mul_one_sub hP hN hright ih (hdown j ih)

/-- Every fixed-state equality representation is a permutation of a constant-rate chain. -/
theorem phase_variance_chain_classification {n : ℕ}
    (P N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hP : Substochastic P) (hN : ∀ i j, 0 ≤ N i j)
    (hleft : (1 - P) * N = 1) (hright : N * (1 - P) = 1)
    (i : Fin (n + 1))
    (heq : ((n + 1 : ℝ) + 1) * (N.mulVec (fun _ ↦ (1 : ℝ)) i) ^ 2 =
      2 * (n + 1 : ℝ) * N.mulVec (N.mulVec (fun _ ↦ (1 : ℝ))) i) :
    ∃ a : ℝ, 0 < a ∧ ∃ e : Fin (n + 1) ≃ Fin (n + 1),
      e (Fin.last n) = i ∧ P.submatrix e e = 1 - a⁻¹ • chainD (n + 1) ∧
        N.submatrix e e = a • chainL (n + 1) := by
  obtain ⟨a, ha, e, htop, hlevels, hlocal⟩ :=
    phase_variance_chain_certificate P N hP hN hleft hright i heq
  let Q := P.submatrix e e
  have hQ : Substochastic Q := by
    constructor
    · intro j k
      exact hP.nonneg (e j) (e k)
    · intro j
      change ∑ k, P (e j) (e k) ≤ 1
      rw [e.sum_comp]
      exact hP.row_sum_le (e j)
  have hbalance (j : Fin (n + 1)) :
      (j.val + 1 : ℝ) * a - ∑ k, Q j k * ((k.val + 1 : ℝ) * a) = 1 := by
    have hm : (1 - P).mulVec (N.mulVec (fun _ ↦ (1 : ℝ))) = fun _ ↦ 1 := by
      rw [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
    have hj := congrFun hm (e j)
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hj
    change N.mulVec (fun _ ↦ (1 : ℝ)) (e j) -
      ∑ k, P (e j) k * N.mulVec (fun _ ↦ (1 : ℝ)) k = 1 at hj
    rw [← e.sum_comp (fun k ↦ P (e j) k * N.mulVec (fun _ ↦ (1 : ℝ)) k)] at hj
    simpa only [hlevels] using hj
  have hsupport (j : Fin (n + 1)) (hj : 0 < N i (e j)) :
      ∀ k, Q j k ≠ 0 → k = j ∨ j.val = k.val + 1 := by
    intro k hk
    have hp : 0 < Q j k := lt_of_le_of_ne (hQ.nonneg j k) hk.symm
    rcases (hlocal j hj).2 k hp with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  have hexit (j : Fin (n + 1)) (hj : 0 < N i (e j)) (hjzero : j.val ≠ 0) :
      ∑ k, Q j k = 1 := by
    have hle := hQ.row_sum_le j
    by_contra hne
    have hlt : ∑ k, Q j k < 1 := lt_of_le_of_ne hle hne
    have hsum : ∑ k, Q j k = ∑ k, P (e j) k := e.sum_comp _
    exact hjzero ((hlocal j hj).1 (by rw [← hsum]; linarith))
  have hrow (j : Fin (n + 1)) (hj : 0 < N i (e j)) :=
    phase_chain_row_form Q ha j (hsupport j hj) (hexit j hj) (hbalance j)
  have hdown (j : Fin n) (hj : 0 < N i (e j.succ)) :
      0 < P (e j.succ) (e j.castSucc) := by
    change 0 < Q j.succ j.castSucc
    rw [phase_chain_row_predecessor Q ha j.succ (hsupport j.succ hj)
      (hexit j.succ hj) (hbalance j.succ) j.castSucc rfl]
    exact one_div_pos.mpr ha
  have hoccupied := chain_all_occupied P N hP.nonneg hN hright e i htop hdown
  have hform : P.submatrix e e = 1 - a⁻¹ • chainD (n + 1) := by
    ext j k
    change Q j k = _
    rw [hrow j (hoccupied j) k]
    by_cases hjk : j = k
    · subst k
      simp [chainD, shiftDown, one_div]
    · by_cases hpred : j.val = k.val + 1
      · simp [hjk, hpred, chainD, shiftDown, one_div]
      · simp [hjk, hpred, chainD, shiftDown]
  exact ⟨a, ha, e, htop, hform, green_eq_chain_of_transition P N e a ha.ne' hright hform⟩

/-- The chain classification stated for an arbitrary positive number of phases. -/
theorem phase_variance_chain_classification_of_pos {s : ℕ} (hs : 0 < s)
    (P N : Matrix (Fin s) (Fin s) ℝ)
    (hP : Substochastic P) (hN : ∀ i j, 0 ≤ N i j)
    (hleft : (1 - P) * N = 1) (hright : N * (1 - P) = 1) (i : Fin s)
    (heq : ((s : ℝ) + 1) * (N.mulVec (fun _ ↦ (1 : ℝ)) i) ^ 2 =
      2 * (s : ℝ) * N.mulVec (N.mulVec (fun _ ↦ (1 : ℝ))) i) :
    ∃ a : ℝ, 0 < a ∧ ∃ e : Fin s ≃ Fin s,
      e ⟨s - 1, by omega⟩ = i ∧ P.submatrix e e = 1 - a⁻¹ • chainD s ∧
        N.submatrix e e = a • chainL s := by
  cases s with
  | zero => omega
  | succ n =>
    exact phase_variance_chain_classification P N hP hN hleft hright i
      (by simpa only [Nat.cast_add, Nat.cast_one] using heq)

end SSPRK
