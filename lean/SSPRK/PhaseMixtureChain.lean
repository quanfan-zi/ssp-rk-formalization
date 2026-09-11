import SSPRK.PhaseChainEquality
import SSPRK.PhaseMixtureEquality
import Mathlib.Order.Interval.Finset.Fin

/-!
# Chain rigidity for sharp phase-type mixtures

A sharp mixture has unit mass at a single top state of a constant-rate descending chain.
-/

open scoped BigOperators

namespace SSPRK

/-- Each cumulative-chain row contains one entry for every level up to that row. -/
lemma chainL_mulVec_one {s : ℕ} (j : Fin s) :
    (chainL s).mulVec (fun _ ↦ (1 : ℝ)) j = (j.val + 1 : ℝ) := by
  simp only [Matrix.mulVec, dotProduct, chainL, mul_one]
  rw [← Finset.sum_filter]
  have hfilter : Finset.univ.filter (fun k : Fin s ↦ k ≤ j) = Finset.Iic j := by
    ext k
    simp
  rw [hfilter]
  simp [Fin.card_Iic]

/-- Reindexing a scaled cumulative Green matrix exposes its strictly increasing row sums. -/
lemma green_chain_mean_levels {s : ℕ} (N : Matrix (Fin s) (Fin s) ℝ)
    (e : Fin s ≃ Fin s) (a : ℝ) (hN : N.submatrix e e = a • chainL s) :
    ∀ j, N.mulVec (fun _ ↦ (1 : ℝ)) (e j) = (j.val + 1 : ℝ) * a := by
  intro j
  have hsum := congrFun (congrArg (fun M : Matrix (Fin s) (Fin s) ℝ ↦
    M.mulVec (fun _ ↦ (1 : ℝ))) hN) j
  dsimp only at hsum
  rw [Matrix.smul_mulVec] at hsum
  simp only [Pi.smul_apply, smul_eq_mul, chainL_mulVec_one] at hsum
  change (∑ k, N (e j) (e k) * 1) = a * (j.val + 1 : ℝ) at hsum
  rw [e.sum_comp (fun k ↦ N (e j) k * 1)] at hsum
  change (∑ k, N (e j) k * 1) = _
  linarith

/-- A sharp nonnegative mixture is concentrated at the top of a constant-rate chain. -/
theorem phase_mixture_chain_classification {n : ℕ}
    (P N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (π : Fin (n + 1) → ℝ)
    (hP : Substochastic P) (hN : ∀ i j, 0 ≤ N i j)
    (hleft : (1 - P) * N = 1) (hright : N * (1 - P) = 1)
    (hπ : ∀ j, 0 ≤ π j) (hmass : ∑ j, π j ≤ 1)
    (hmean : 0 < dotProduct π (N.mulVec (fun _ ↦ (1 : ℝ))))
    (heq : ((n + 1 : ℝ) + 1) * (dotProduct π (N.mulVec (fun _ ↦ (1 : ℝ)))) ^ 2 =
      2 * (n + 1 : ℝ) * dotProduct π (N.mulVec (N.mulVec (fun _ ↦ (1 : ℝ))))) :
    ∃ a : ℝ, 0 < a ∧ ∃ e : Fin (n + 1) ≃ Fin (n + 1),
      P.submatrix e e = 1 - a⁻¹ • chainD (n + 1) ∧
      N.submatrix e e = a • chainL (n + 1) ∧
      (∀ j, π (e j) = if j = Fin.last n then 1 else 0) ∧
      dotProduct π (N.mulVec (fun _ ↦ (1 : ℝ))) = (n + 1 : ℝ) * a := by
  let m := N.mulVec (fun _ ↦ (1 : ℝ))
  have hm : ∀ j, 0 ≤ m j := fun j ↦ (green_mean_pos P N hP hN hleft j).le
  obtain ⟨f, _, hlower, hupper, hdiff⟩ := exists_variance_potential (n + 1) m hm
  have hpoint : ∀ j, ((n + 1 : ℝ) + 1) * m j ^ 2 ≤ 2 * (n + 1 : ℝ) * N.mulVec m j :=
    phase_variance_pointwise_of_potential P N f (n + 1) hP hN (by positivity)
      hleft hright (by simpa only [Nat.cast_add, Nat.cast_one] using hlower) hupper hdiff
  obtain ⟨hmass_eq, hsupport⟩ :=
    phase_mixture_equality π m (N.mulVec m) (n + 1) (by positivity) hπ hmass hmean hpoint heq
  have hex : ∃ j, 0 < π j := by
    by_contra h
    push Not at h
    have hs : ∑ j, π j ≤ 0 := Finset.sum_nonpos fun j _ ↦ h j
    linarith
  obtain ⟨i, hi⟩ := hex
  obtain ⟨a, ha, e, htop, hPform, hNform⟩ :=
    phase_variance_chain_classification P N hP hN hleft hright i (hsupport i hi).2
  have hlevels := green_chain_mean_levels N e a hNform
  have hmean_eq : dotProduct π m = (n + 1 : ℝ) * a := by
    rw [← (hsupport i hi).1, ← htop]
    exact hlevels (Fin.last n)
  have hzero (j : Fin (n + 1)) (hj : j ≠ Fin.last n) : π (e j) = 0 := by
    by_contra hz
    have hp : 0 < π (e j) := lt_of_le_of_ne (hπ (e j)) (Ne.symm hz)
    have hmj := (hsupport (e j) hp).1
    change N.mulVec (fun _ ↦ (1 : ℝ)) (e j) = dotProduct π m at hmj
    rw [hlevels, hmean_eq] at hmj
    have hv : (j.val : ℝ) = n := by nlinarith only [hmj, ha]
    exact hj (Fin.ext (by exact_mod_cast hv))
  have hsum : ∑ j, π (e j) = 1 := (e.sum_comp π).trans hmass_eq
  have hsingle : ∑ j, π (e j) = π (e (Fin.last n)) := by
    apply Finset.sum_eq_single (Fin.last n)
    · intro j _ hj
      exact hzero j hj
    · simp
  have htop_weight : π (e (Fin.last n)) = 1 := hsingle.symm.trans hsum
  refine ⟨a, ha, e, hPform, hNform, ?_, hmean_eq⟩
  intro j
  by_cases hj : j = Fin.last n
  · simp [hj, htop_weight]
  · simp [hj, hzero j hj]

/-- Sharp mixture classification for an arbitrary positive phase count. -/
theorem phase_mixture_chain_classification_of_pos {s : ℕ} (hs : 0 < s)
    (P N : Matrix (Fin s) (Fin s) ℝ) (π : Fin s → ℝ)
    (hP : Substochastic P) (hN : ∀ i j, 0 ≤ N i j)
    (hleft : (1 - P) * N = 1) (hright : N * (1 - P) = 1)
    (hπ : ∀ j, 0 ≤ π j) (hmass : ∑ j, π j ≤ 1)
    (hmean : 0 < dotProduct π (N.mulVec (fun _ ↦ (1 : ℝ))))
    (heq : ((s : ℝ) + 1) * (dotProduct π (N.mulVec (fun _ ↦ (1 : ℝ)))) ^ 2 =
      2 * (s : ℝ) * dotProduct π (N.mulVec (N.mulVec (fun _ ↦ (1 : ℝ))))) :
    ∃ a : ℝ, 0 < a ∧ ∃ e : Fin s ≃ Fin s,
      P.submatrix e e = 1 - a⁻¹ • chainD s ∧ N.submatrix e e = a • chainL s ∧
      (∀ j, π (e j) = if j = ⟨s - 1, by omega⟩ then 1 else 0) ∧
      dotProduct π (N.mulVec (fun _ ↦ (1 : ℝ))) = (s : ℝ) * a := by
  cases s with
  | zero => omega
  | succ n =>
    simpa only [Nat.cast_add, Nat.cast_one] using
      phase_mixture_chain_classification P N π hP hN hleft hright hπ hmass hmean
        (by simpa only [Nat.cast_add, Nat.cast_one] using heq)

end SSPRK
