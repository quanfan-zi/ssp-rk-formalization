import SSPRK.PhaseTypeThirdEquality

/-!
# Equality in the third-moment bound for a phase-type mixture

Sharpness of the mixture third-moment bound forces every positively weighted row
to be sharp with a common second-to-first moment ratio.  The pointwise phase-type
equality theorem then turns this into the mass-corrected second-moment equality.
-/

open scoped BigOperators

namespace SSPRK

/-- A sharp finite third-moment mixture inherits a mass-corrected second equality
when every supported sharp component satisfies its second equality. -/
theorem MomentClass.finite_mixture_second_eq_of_third_eq
    {ι : Type*} [Fintype ι] {k : ℝ} (π m1 m2 m3 : ι → ℝ)
    (hπ : ∀ i, 0 ≤ π i) (hx : ∀ i, MomentClass k (m1 i) (m2 i) (m3 i))
    (hmean : 0 < ∑ i, π i * m1 i)
    (hrow : ∀ i, 0 < π i →
      (k + 2) * m2 i ^ 2 = (k + 1) * m1 i * m3 i →
      (k + 1) * m1 i ^ 2 = k * m2 i)
    (heq : (k + 2) * (∑ i, π i * m2 i) ^ 2 =
      (k + 1) * (∑ i, π i * m1 i) * (∑ i, π i * m3 i)) :
    (k + 1) * (∑ i, π i * m1 i) ^ 2 =
      k * (∑ i, π i) * (∑ i, π i * m2 i) := by
  obtain ⟨q, hq⟩ :=
    (MomentClass.finite_mixture_third_eq_iff π m1 m2 m3 hπ hx hmean).mp heq
  have hm2 : ∑ i, π i * m2 i = q * ∑ i, π i * m1 i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    obtain hzero | hpos := (hπ i).eq_or_lt
    · simp [← hzero]
    · have hratio := (div_eq_iff (hx i).mean_pos.ne').mp (hq i hpos).2
      rw [hratio]
      ring
  have hlinear (i : ι) (hi : 0 < π i) : (k + 1) * m1 i = k * q := by
    have hsecond := hrow i hi (hq i hi).1
    have hratio := (div_eq_iff (hx i).mean_pos.ne').mp (hq i hi).2
    apply mul_right_cancel₀ (hx i).mean_pos.ne'
    calc
      ((k + 1) * m1 i) * m1 i = (k + 1) * m1 i ^ 2 := by ring
      _ = k * m2 i := hsecond
      _ = (k * q) * m1 i := by rw [hratio]; ring
  have hsum : (k + 1) * (∑ i, π i * m1 i) = k * q * ∑ i, π i := by
    calc
      (k + 1) * (∑ i, π i * m1 i) =
          ∑ i, π i * ((k + 1) * m1 i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i, π i * (k * q) := by
        apply Finset.sum_congr rfl
        intro i _
        obtain hzero | hpos := (hπ i).eq_or_lt
        · simp [← hzero]
        · rw [hlinear i hpos]
      _ = k * q * ∑ i, π i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  calc
    (k + 1) * (∑ i, π i * m1 i) ^ 2 =
        ((k + 1) * ∑ i, π i * m1 i) * (∑ i, π i * m1 i) := by ring
    _ = (k * q * ∑ i, π i) * (∑ i, π i * m1 i) := by rw [hsum]
    _ = k * (∑ i, π i) * (∑ i, π i * m2 i) := by rw [hm2]; ring

namespace PhaseTypeData

private def pointInitial {s : ℕ} (d : PhaseTypeData s) (i : Fin s) :
    PhaseTypeData s where
  transition := d.transition
  initial := fun j ↦ if j = i then 1 else 0
  rate := d.rate
  rate_pos := d.rate_pos
  substochastic := d.substochastic
  transient := d.transient
  initial_nonneg := by
    intro j
    split_ifs <;> norm_num
  initial_mass_le := by simp

private lemma pointInitial_green {s : ℕ} (d : PhaseTypeData s) (i : Fin s) :
    (pointInitial d i).green = d.green := rfl

private lemma pointInitial_dotProduct {s : ℕ} (d : PhaseTypeData s) (i : Fin s)
    (x : Fin s → ℝ) :
    dotProduct (pointInitial d i).initial x = x i := by
  simp [pointInitial, dotProduct]

private lemma green_row_moment_class {s : ℕ} (d : PhaseTypeData s) (i : Fin s) :
    MomentClass s (d.green.mulVec (fun _ ↦ 1) i)
      (2 * (d.green ^ 2).mulVec (fun _ ↦ 1) i)
      (6 * (d.green ^ 3).mulVec (fun _ ↦ 1) i) := by
  have hclass := green_moment_class s (pointInitial d i) (by
    rw [pointInitial_green, pointInitial_dotProduct]
    exact d.green_rowSum_pos i)
  simpa only [pointInitial_green, pointInitial_dotProduct] using hclass

/-- Sharpness of the aggregate Green third-moment bound forces the second-moment
equality corrected by the transient initial mass. -/
theorem green_mixture_second_eq_of_third_eq {s : ℕ} (d : PhaseTypeData s)
    (hmean : 0 < dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)))
    (heq : ((s : ℝ) + 2) *
        (2 * dotProduct d.initial ((d.green ^ 2).mulVec (fun _ ↦ 1))) ^ 2 =
      ((s : ℝ) + 1) * dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)) *
        (6 * dotProduct d.initial ((d.green ^ 3).mulVec (fun _ ↦ 1)))) :
    ((s : ℝ) + 1) * dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)) ^ 2 =
      (s : ℝ) * d.mass *
        (2 * dotProduct d.initial ((d.green ^ 2).mulVec (fun _ ↦ 1))) := by
  have hs : 0 < s := by
    cases s with
    | zero => simp [dotProduct] at hmean
    | succ n => exact Nat.succ_pos n
  let m1 := fun i ↦ d.green.mulVec (fun _ ↦ 1) i
  let m2 := fun i ↦ 2 * (d.green ^ 2).mulVec (fun _ ↦ 1) i
  let m3 := fun i ↦ 6 * (d.green ^ 3).mulVec (fun _ ↦ 1) i
  have hclass : ∀ i, MomentClass s (m1 i) (m2 i) (m3 i) := by
    intro i
    exact d.green_row_moment_class i
  have hresult := MomentClass.finite_mixture_second_eq_of_third_eq
    d.initial m1 m2 m3 d.initial_nonneg hclass (by
      simpa only [m1, dotProduct] using hmean) (fun i hi hsharp ↦ by
        exact d.green_second_eq_of_third_eq hs i hsharp) (by
      simpa only [m1, m2, m3, dotProduct, Finset.mul_sum, mul_left_comm] using heq)
  simpa only [m1, m2, dotProduct, mass, Finset.mul_sum, mul_left_comm] using hresult

end PhaseTypeData
end SSPRK
