import SSPRK.MidpointAttainment
import SSPRK.PhaseMixtureChain

/-!
# Uniqueness of the optimal second-order tableau

The equality classification determines the transformed chain up to a simultaneous
permutation.  This file applies the inverse Runge--Kutta transform to recover the original coefficients. Radius corollaries are kept separately.
-/

open scoped BigOperators ENNReal

namespace SSPRK

noncomputable section

/-- A sorted Green chain with scale two and its terminal initial mass recover the midpoint tableau. -/
theorem eq_midpoint_of_sorted_transform {s : ℕ} (hs : 0 < s)
    (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ)
    (e : Fin s ≃ Fin s) (ham : AbsolutelyMonotoneAt A b (2 * (s : ℝ)))
    (hN : (rkN (2 * (s : ℝ)) A).submatrix e e = (2 : ℝ) • chainL s)
    (hω : ∀ j, rkOmega (2 * (s : ℝ)) b A (e j) =
      if j = ⟨s - 1, by omega⟩ then 1 else 0) :
    A.submatrix e e = midpointA s ∧ (fun j ↦ b (e j)) = midpointB s := by
  let r : ℝ := 2 * (s : ℝ)
  let last : Fin s := ⟨s - 1, by omega⟩
  have hr : r = 2 * (s : ℝ) := rfl
  have hrpos : 0 < r := by
    dsimp only [r]
    positivity
  have hsubN : (rkN r A).submatrix e e = 1 + r • A.submatrix e e := by
    ext i j
    simp [rkN, Matrix.submatrix, Matrix.one_apply]
  have hshiftA : 1 + r • A.submatrix e e = (2 : ℝ) • chainL s := by
    rw [← hsubN, hr]
    exact hN
  have hshiftMidpoint : 1 + r • midpointA s = (2 : ℝ) • chainL s := by
    rw [hr]
    exact midpoint_shifted_matrix hs
  have hA : A.submatrix e e = midpointA s := by
    ext i j
    have hij := congrArg (fun M : Matrix (Fin s) (Fin s) ℝ ↦ M i j)
      (hshiftA.trans hshiftMidpoint.symm)
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hij
    nlinarith
  have hvec (j : Fin s) :
      Matrix.vecMul (rkOmega r b A) (rkN r A) (e j) = 2 := by
    change (∑ i, rkOmega r b A i * rkN r A i (e j)) = 2
    rw [← e.sum_comp]
    simp_rw [hr, hω]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hentry := congrArg (fun M : Matrix (Fin s) (Fin s) ℝ ↦ M last j) hN
    have hjlast : j ≤ last := by
      rw [Fin.le_iff_val_le_val]
      dsimp only [last]
      omega
    simpa [last, Matrix.submatrix, chainL, hjlast] using hentry
  refine ⟨hA, ?_⟩
  ext j
  have hj := congrFun (rkOmega_vecMul_rkN r b A ham.det_ne_zero) (e j)
  rw [hvec] at hj
  simp only [Pi.smul_apply, smul_eq_mul] at hj
  simp only [midpointB]
  rw [hr] at hj
  have hsreal : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hs)
  field_simp [hsreal]
  nlinarith

/-- A second-order tableau feasible at `2s` is the midpoint tableau up to permutation. -/
theorem second_order_classification_at_bound {s : ℕ} (hs : 0 < s)
    (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ)
    (hord1 : dotProduct b (ones s) = 1)
    (hord2 : dotProduct b (A.mulVec (ones s)) = 1 / 2)
    (ham : AbsolutelyMonotoneAt A b (2 * (s : ℝ))) :
    ∃ e : Fin s ≃ Fin s,
      A.submatrix e e = midpointA s ∧ (fun j ↦ b (e j)) = midpointB s := by
  let r : ℝ := 2 * (s : ℝ)
  let P := rkP r A
  let N := rkN r A
  let π := rkOmega r b A
  have hr : r = 2 * (s : ℝ) := rfl
  have hrpos : 0 < r := by
    dsimp only [r]
    positivity
  have hP : Substochastic P := by
    exact rkP_substochastic r A ham.det_ne_zero ham.stages ham.matrix_nonneg
  have hN : ∀ i j, 0 ≤ N i j := rkN_nonneg r A ham.det_ne_zero hP
  have hleft : (1 - P) * N = 1 := by
    dsimp only [P, N]
    rw [one_sub_rkP_eq_rkM]
    exact rkM_mul_rkN r A ham.det_ne_zero
  have hright : N * (1 - P) = 1 := by
    dsimp only [P, N]
    rw [one_sub_rkP_eq_rkM]
    exact rkN_mul_rkM r A ham.det_ne_zero
  have hπ : ∀ j, 0 ≤ π j := by
    exact rkOmega_nonneg r b A hrpos.le ham.output_nonneg
  have hmass : ∑ j, π j ≤ 1 := by
    simpa [π, rkSigma, ones, dotProduct] using rkSigma_le_one r b A ham.output_mass
  have hfirst : dotProduct π (N.mulVec (ones s)) = r := by
    dsimp only [π, N]
    rw [Matrix.dotProduct_mulVec]
    exact rkOmega_N_ones_eq r b A ham.det_ne_zero hord1
  have hsecond : dotProduct π (N.mulVec (N.mulVec (ones s))) = r + r ^ 2 / 2 := by
    dsimp only [π, N]
    rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    exact rkOmega_N_sq_ones_eq r b A ham.det_ne_zero hord1 hord2
  have hmean : 0 < dotProduct π (N.mulVec (ones s)) := by
    rw [hfirst]
    exact hrpos
  have heq : ((s : ℝ) + 1) * (dotProduct π (N.mulVec (ones s))) ^ 2 =
      2 * (s : ℝ) * dotProduct π (N.mulVec (N.mulVec (ones s))) := by
    rw [hfirst, hsecond, hr]
    ring
  obtain ⟨a, ha, e, _, hNform, hπform, hmean_eq⟩ :=
    phase_mixture_chain_classification_of_pos hs P N π hP hN hleft hright hπ hmass hmean heq
  have ha_eq : a = 2 := by
    change dotProduct π (N.mulVec (ones s)) = (s : ℝ) * a at hmean_eq
    rw [hfirst, hr] at hmean_eq
    have hsreal : 0 < (s : ℝ) := Nat.cast_pos.mpr hs
    nlinarith
  have hNtwo : (rkN (2 * (s : ℝ)) A).submatrix e e =
      (2 : ℝ) • chainL s := by
    dsimp only [N] at hNform
    rw [hr] at hNform
    simpa only [ha_eq] using hNform
  exact ⟨e, eq_midpoint_of_sorted_transform hs A b e ham hNtwo hπform⟩

end

end SSPRK
