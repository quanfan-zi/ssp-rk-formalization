import SSPRK.MomentMixture

/-!
# Two finite Cauchy--Schwarz inequalities for complete homogeneous polynomials

The composition weights used in Schur's inequality are nonnegative. The first
Cauchy--Schwarz inequality is within one composition and the second is over all
compositions. The equality statement keeps the first inequality sharp on every
positive-weight composition.
-/

open scoped BigOperators

namespace SSPRK

/-- A weighted finite Cauchy--Schwarz inequality, without square roots. -/
lemma finite_weighted_square_le {ι : Type*} (u : Finset ι) (w t : ι → ℝ)
    (hw : ∀ a ∈ u, 0 ≤ w a) :
    (∑ a ∈ u, w a * t a) ^ 2 ≤ (∑ a ∈ u, w a) * ∑ a ∈ u, w a * t a ^ 2 := by
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul u hw
    (fun a ha ↦ mul_nonneg (hw a ha) (sq_nonneg (t a)))
    (fun a _ ↦ le_of_eq (by ring))

/-- Combining the local and global Cauchy--Schwarz bounds. -/
lemma finite_weighted_schur {ι : Type*} (u : Finset ι) (w t q : ι → ℝ)
    (p : ℝ) (hp : 0 < p) (hw : ∀ a ∈ u, 0 ≤ w a)
    (hlocal : ∀ a ∈ u, t a ^ 2 ≤ p * q a) :
    (p + 1) * (∑ a ∈ u, w a * t a) ^ 2 ≤
      p * (∑ a ∈ u, w a) * ∑ a ∈ u, w a * (t a ^ 2 + q a) := by
  have hcs := finite_weighted_square_le u w t hw
  have hstep : (p + 1) * (∑ a ∈ u, w a * t a ^ 2) ≤
      p * (∑ a ∈ u, w a * (t a ^ 2 + q a)) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_le_sum fun a ha ↦ by
      nlinarith only [mul_nonneg (hw a ha) (sub_nonneg.mpr (hlocal a ha))]
  calc
    _ ≤ (p + 1) * ((∑ a ∈ u, w a) * ∑ a ∈ u, w a * t a ^ 2) :=
      mul_le_mul_of_nonneg_left hcs (by linarith only [hp])
    _ = (∑ a ∈ u, w a) * ((p + 1) * ∑ a ∈ u, w a * t a ^ 2) := by ring
    _ ≤ (∑ a ∈ u, w a) * (p * ∑ a ∈ u, w a * (t a ^ 2 + q a)) :=
      mul_le_mul_of_nonneg_left hstep (Finset.sum_nonneg hw)
    _ = _ := by ring

/-- Sharpness of the combined bound makes every positive-weight local bound sharp. -/
lemma finite_weighted_schur_eq_local {ι : Type*} (u : Finset ι) (w t q : ι → ℝ)
    (p : ℝ) (hp : 0 < p) (hw : ∀ a ∈ u, 0 ≤ w a)
    (hlocal : ∀ a ∈ u, t a ^ 2 ≤ p * q a) (hmass : 0 < ∑ a ∈ u, w a)
    (heq : (p + 1) * (∑ a ∈ u, w a * t a) ^ 2 =
      p * (∑ a ∈ u, w a) * ∑ a ∈ u, w a * (t a ^ 2 + q a)) :
    ∀ a ∈ u, 0 < w a → t a ^ 2 = p * q a := by
  have hcs := mul_le_mul_of_nonneg_left (finite_weighted_square_le u w t hw)
    (show 0 ≤ p + 1 by linarith only [hp])
  have hid : (∑ a ∈ u, w a * (p * q a - t a ^ 2)) =
      p * (∑ a ∈ u, w a * (t a ^ 2 + q a)) -
        (p + 1) * (∑ a ∈ u, w a * t a ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  have hzero : (∑ a ∈ u, w a * (p * q a - t a ^ 2)) = 0 := by
    apply le_antisymm
    · apply (mul_le_mul_iff_right₀ hmass).mp
      rw [hid]
      nlinarith only [heq, hcs]
    · exact Finset.sum_nonneg fun a ha ↦
        mul_nonneg (hw a ha) (sub_nonneg.mpr (hlocal a ha))
  intro a ha hwa
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun a ha ↦ mul_nonneg (hw a ha) (sub_nonneg.mpr (hlocal a ha)))).mp hzero a ha
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hwa.ne')).symm

end SSPRK
