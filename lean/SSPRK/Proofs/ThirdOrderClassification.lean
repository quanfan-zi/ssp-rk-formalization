import SSPRK.PhaseTypeThirdLaw
import SSPRK.RKThirdMoment
import SSPRK.SDIRKAttainment

/-!
# Uniqueness of sharp third-order tableaux

Third-moment equality makes the Runge--Kutta phase-type Green matrix a constant-rate chain.
The inverse transform then identifies the SDIRK tableau, up to a simultaneous permutation.
-/

open scoped BigOperators ENNReal

namespace SSPRK

noncomputable section

lemma thirdOrderRadius_quadratic_eq_zero {s : ℕ} (hs : 2 ≤ s) :
    thirdOrderRadius s ^ 2 - 2 * ((s : ℝ) - 1) * thirdOrderRadius s -
      2 * ((s : ℝ) - 1) = 0 := by
  change ((s : ℝ) - 1 + sdirkT s) ^ 2 - 2 * ((s : ℝ) - 1) *
      ((s : ℝ) - 1 + sdirkT s) - 2 * ((s : ℝ) - 1) = 0
  nlinarith [sdirkT_sq hs]

lemma thirdOrderRadius_add_two_div_succ_eq_sdirkD {s : ℕ} (hs : 2 ≤ s) :
    (thirdOrderRadius s + 2) / ((s : ℝ) + 1) = sdirkD s := by
  have ht : sdirkT s ≠ 0 := ne_of_gt (sdirkT_pos hs)
  have hspos : 0 < (s : ℝ) + 1 := by positivity
  change (((s : ℝ) - 1 + sdirkT s) + 2) / ((s : ℝ) + 1) =
    1 + ((s : ℝ) - 1) / sdirkT s
  field_simp [ht, hspos.ne']
  nlinarith [sdirkT_sq hs]

/-- A sorted shifted chain with the correct mean recovers the SDIRK tableau. -/
theorem eq_sdirk_of_sorted_transform {s : ℕ} (hs : 2 ≤ s)
    (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ) (e : Fin s ≃ Fin s)
    (ham : AbsolutelyMonotoneAt A b (thirdOrderRadius s)) (m : ℝ)
    (hN : (rkN (thirdOrderRadius s) A).submatrix e e = sdirkD s • chainL s)
    (hω : ∀ j, rkOmega (thirdOrderRadius s) b A (e j) =
      if j = ⟨s - 1, by omega⟩ then m else 0)
    (hmean : thirdOrderRadius s = m * (s : ℝ) * sdirkD s) :
    A.submatrix e e = sdirkA s ∧ (fun j ↦ b (e j)) = sdirkB s := by
  let r : ℝ := thirdOrderRadius s
  let last : Fin s := ⟨s - 1, by omega⟩
  have hr : r = thirdOrderRadius s := rfl
  have hrpos : 0 < r := by simpa [r] using thirdOrderRadius_pos hs
  have hsubN : (rkN r A).submatrix e e = 1 + r • A.submatrix e e := by
    ext i j
    simp [rkN, Matrix.submatrix, Matrix.one_apply]
  have hshiftA : 1 + r • A.submatrix e e = sdirkD s • chainL s := by
    rw [← hsubN, hr]
    exact hN
  have hshiftSDIRK : 1 + r • sdirkA s = sdirkD s • chainL s := by
    rw [hr]
    exact sdirk_shifted_eq_chainL hs
  have hA : A.submatrix e e = sdirkA s := by
    ext i j
    have hij := congrArg (fun M : Matrix (Fin s) (Fin s) ℝ ↦ M i j)
      (hshiftA.trans hshiftSDIRK.symm)
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hij
    nlinarith
  have hvec (j : Fin s) :
      Matrix.vecMul (rkOmega r b A) (rkN r A) (e j) = m * sdirkD s := by
    have hωlast (i : Fin s) : rkOmega r b A (e i) = if i = last then m else 0 := by
      simpa [hr, last] using hω i
    change (∑ i, rkOmega r b A i * rkN r A i (e j)) = m * sdirkD s
    rw [← e.sum_comp]
    simp_rw [hωlast]
    rw [Finset.sum_eq_single last]
    · simp only [if_pos]
      have hentry := congrArg (fun M : Matrix (Fin s) (Fin s) ℝ ↦ M last j) hN
      have hjlast : j ≤ last := by
        rw [Fin.le_iff_val_le_val]
        dsimp only [last]
        omega
      simpa [hr, last, Matrix.submatrix, chainL, hjlast] using
        congrArg (fun x ↦ m * x) hentry
    · intro i _ hi
      simp [hi]
    · simp
  refine ⟨hA, ?_⟩
  ext j
  have hj := congrFun (rkOmega_vecMul_rkN r b A ham.det_ne_zero) (e j)
  rw [hvec] at hj
  simp only [Pi.smul_apply, smul_eq_mul] at hj
  simp only [sdirkB]
  change r = m * (s : ℝ) * sdirkD s at hmean
  have hsreal : 0 < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hrnonzero : thirdOrderRadius s ≠ 0 := ne_of_gt (thirdOrderRadius_pos hs)
  field_simp [hsreal.ne', hrnonzero] at hj hmean ⊢
  nlinarith

theorem third_order_classification_at_bound {s : ℕ} (hs : 2 ≤ s)
    (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ)
    (hord1 : dotProduct b (fun _ ↦ (1 : ℝ)) = 1)
    (hord2 : dotProduct b (A.mulVec (fun _ ↦ (1 : ℝ))) = 1 / 2)
    (hord3 : dotProduct b ((A * A).mulVec (fun _ ↦ (1 : ℝ))) = 1 / 6)
    (ham : AbsolutelyMonotoneAt A b (thirdOrderRadius s)) :
    ∃ e : Fin s ≃ Fin s,
      A.submatrix e e = sdirkA s ∧ (fun j ↦ b (e j)) = sdirkB s := by
  let r : ℝ := thirdOrderRadius s
  let d := ham.phaseType (thirdOrderRadius_pos hs)
  have hr : r = thirdOrderRadius s := rfl
  have hrpos : 0 < r := by simpa [r] using thirdOrderRadius_pos hs
  have hdgreen : d.green = rkN (thirdOrderRadius s) A := by
    dsimp only [d]
    exact ham.phaseType_green (thirdOrderRadius_pos hs)
  have hraw1 : dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)) = r := by
    change dotProduct (rkOmega (thirdOrderRadius s) b A) (d.green.mulVec (fun _ ↦ 1)) = r
    rw [hdgreen]
    rw [Matrix.dotProduct_mulVec]
    rw [hr]
    exact rkOmega_N_ones_eq _ _ _ ham.det_ne_zero hord1
  have hraw2 : 2 * dotProduct d.initial ((d.green ^ 2).mulVec (fun _ ↦ 1)) = r ^ 2 + 2 * r := by
    change 2 * dotProduct (rkOmega (thirdOrderRadius s) b A)
      ((d.green ^ 2).mulVec (fun _ ↦ 1)) = _
    rw [hdgreen, pow_two, Matrix.dotProduct_mulVec]
    have h := rkOmega_N_sq_ones_eq (thirdOrderRadius s) b A ham.det_ne_zero hord1 hord2
    have h' : dotProduct (Matrix.vecMul (rkOmega (thirdOrderRadius s) b A)
        (rkN (thirdOrderRadius s) A * rkN (thirdOrderRadius s) A)) (fun _ ↦ 1) =
        r + r ^ 2 / 2 := by simpa [← hr, ones] using h
    nlinarith [h']
  have hraw3 : 6 * dotProduct d.initial ((d.green ^ 3).mulVec (fun _ ↦ 1)) =
      r ^ 3 + 6 * r ^ 2 + 6 * r := by
    change 6 * dotProduct (rkOmega (thirdOrderRadius s) b A)
      ((d.green ^ 3).mulVec (fun _ ↦ 1)) = _
    rw [hdgreen]
    rw [show rkN (thirdOrderRadius s) A ^ 3 =
        rkN (thirdOrderRadius s) A * rkN (thirdOrderRadius s) A * rkN (thirdOrderRadius s) A by
      rw [pow_succ, pow_two, Matrix.mul_assoc]]
    rw [Matrix.dotProduct_mulVec]
    have h := rkOmega_N_cu_ones_eq (thirdOrderRadius s) b A ham.det_ne_zero hord1 hord2 hord3
    have h' : dotProduct (Matrix.vecMul (rkOmega (thirdOrderRadius s) b A)
        (rkN (thirdOrderRadius s) A * rkN (thirdOrderRadius s) A * rkN (thirdOrderRadius s) A))
        (fun _ ↦ 1) = r + r ^ 2 + r ^ 3 / 6 := by simpa [← hr, ones] using h
    nlinarith [h']
  have hroot : r ^ 2 - 2 * ((s : ℝ) - 1) * r - 2 * ((s : ℝ) - 1) = 0 := by
    rw [hr]
    exact thirdOrderRadius_quadratic_eq_zero hs
  have heq : ((s : ℝ) + 2) *
      (2 * dotProduct d.initial ((d.green ^ 2).mulVec (fun _ ↦ 1))) ^ 2 =
      ((s : ℝ) + 1) * dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)) *
        (6 * dotProduct d.initial ((d.green ^ 3).mulVec (fun _ ↦ 1))) := by
    rw [hraw1, hraw2, hraw3]
    nlinarith [hroot]
  have hmean : 0 < dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)) := by
    rw [hraw1]
    exact hrpos
  obtain ⟨a, ha, e, _, hgreen, hinitial, hfirst⟩ :=
    d.third_equality_representation (by omega) hmean heq
  have hsecond := d.third_equality_second_moment (by omega) hmean heq a hfirst
  have hcombined : r ^ 2 + 2 * r = r * a * ((s : ℝ) + 1) := by
    rw [← hraw2, hsecond]
    calc
      d.mass * a ^ 2 * (s : ℝ) * ((s : ℝ) + 1) =
          (d.mass * (s : ℝ) * a) * a * ((s : ℝ) + 1) := by ring
      _ = r * a * ((s : ℝ) + 1) := by rw [← hfirst, hraw1]
  have ha_formula : a = (r + 2) / ((s : ℝ) + 1) := by
    apply (eq_div_iff (by positivity : (s : ℝ) + 1 ≠ 0)).mpr
    nlinarith [hcombined, hrpos]
  have ha_eq : a = sdirkD s := by
    rw [ha_formula, hr]
    exact thirdOrderRadius_add_two_div_succ_eq_sdirkD hs
  have hN : (rkN (thirdOrderRadius s) A).submatrix e e = sdirkD s • chainL s := by
    have hdgreen : d.green = rkN (thirdOrderRadius s) A := by
      dsimp only [d]
      exact ham.phaseType_green (thirdOrderRadius_pos hs)
    rw [← hdgreen]
    simpa only [ha_eq] using hgreen
  have homega : ∀ j, rkOmega (thirdOrderRadius s) b A (e j) =
      if j = ⟨s - 1, by omega⟩ then d.mass else 0 := by
    intro j
    simpa only [d, AbsolutelyMonotoneAt.phaseType] using hinitial j
  have hmean' : thirdOrderRadius s = d.mass * (s : ℝ) * sdirkD s := by
    calc
      thirdOrderRadius s = r := hr.symm
      _ = dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)) := hraw1.symm
      _ = d.mass * (s : ℝ) * sdirkD s := by rw [hfirst, ha_eq]
  exact ⟨e, eq_sdirk_of_sorted_transform hs A b e ham d.mass hN homega hmean'⟩

end

end SSPRK
