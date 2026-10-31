import SSPRK.MomentAlgebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp

/-! Finite mixtures, including a residual atom at zero, preserve the moment classes. -/

open scoped BigOperators

namespace SSPRK

lemma weighted_quadratic_bound {ι : Type*} [Fintype ι]
    (π x y z : ι → ℝ) {c d : ℝ} (hc : 0 < c) (hd : 0 ≤ d)
    (hπ : ∀ i, 0 ≤ π i) (hx : ∀ i, 0 ≤ x i) (hz : ∀ i, 0 ≤ z i)
    (h : ∀ i, c * y i ^ 2 ≤ d * x i * z i) :
    c * (∑ i, π i * y i) ^ 2 ≤ d * (∑ i, π i * x i) * ∑ i, π i * z i := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i ↦ c * (π i * y i))
    (f := fun i ↦ c * (π i * x i)) (g := fun i ↦ d * (π i * z i))
    (fun i _ ↦ mul_nonneg hc.le (mul_nonneg (hπ i) (hx i)))
    (fun i _ ↦ mul_nonneg hd (mul_nonneg (hπ i) (hz i)))
    (fun i _ ↦ by
      nlinarith only [mul_nonneg (mul_nonneg hc.le (sq_nonneg (π i)))
        (sub_nonneg.mpr (h i))])
  simp only [← Finset.mul_sum] at hcs
  apply (mul_le_mul_iff_right₀ hc).mp
  nlinarith only [hcs]

/-- A finite mixture may assign its remaining probability mass to zero.
-/
theorem MomentClass.finite_mixture {ι : Type*} [Fintype ι]
    {k : ℝ} (π m1 m2 m3 : ι → ℝ) (hπ : ∀ i, 0 ≤ π i)
    (hmass : ∑ i, π i ≤ 1) (hx : ∀ i, MomentClass k (m1 i) (m2 i) (m3 i))
    (hmean : 0 < ∑ i, π i * m1 i) :
    MomentClass k (∑ i, π i * m1 i) (∑ i, π i * m2 i) (∑ i, π i * m3 i) := by
  have hk : 0 < k := by
    obtain ⟨i, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hmean.ne'
    exact (hx i).parameter_pos
  have hsecond : 0 ≤ ∑ i, π i * m2 i :=
    Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hπ i) (hx i).second_nonneg)
  refine ⟨hk, hmean, hsecond,
    Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hπ i) (hx i).third_nonneg), ?_, ?_⟩
  · have h := weighted_quadratic_bound π (fun _ ↦ 1) m1 m2
      (by linarith : 0 < k + 1) hk.le hπ (fun _ ↦ zero_le_one)
      (fun i ↦ (hx i).second_nonneg) (fun i ↦ by simpa using (hx i).second_bound)
    simp only [mul_one] at h
    nlinarith only [h, mul_nonneg (mul_nonneg hk.le hsecond) (sub_nonneg.mpr hmass)]
  · exact weighted_quadratic_bound π m1 m2 m3 (by linarith : 0 < k + 2)
      (by linarith) hπ (fun i ↦ (hx i).mean_pos.le) (fun i ↦ (hx i).third_nonneg)
      (fun i ↦ (hx i).third_bound)

theorem weighted_quadratic_eq_iff {ι : Type*} [Fintype ι]
    (π x y z : ι → ℝ) {c d : ℝ} (hc : 0 < c)
    (hπ : ∀ i, 0 ≤ π i) (hx : ∀ i, 0 < x i)
    (h : ∀ i, c * y i ^ 2 ≤ d * x i * z i)
    (hmean : 0 < ∑ i, π i * x i) :
    c * (∑ i, π i * y i) ^ 2 = d * (∑ i, π i * x i) * (∑ i, π i * z i) ↔
      ∃ q : ℝ, ∀ i, 0 < π i →
        c * y i ^ 2 = d * x i * z i ∧ y i = q * x i := by
  let sx := ∑ i, π i * x i
  let sy := ∑ i, π i * y i
  let sz := ∑ i, π i * z i
  change c * sy ^ 2 = d * sx * sz ↔ _
  have hsx : 0 < sx := hmean
  constructor
  · intro heq
    let q := sy / sx
    let residual := fun i ↦ d * z i - 2 * c * q * y i + c * q ^ 2 * x i
    have hres (i : ι) : 0 ≤ residual i := by
      apply nonneg_of_mul_nonneg_left (b := x i) ?_ (hx i)
      dsimp only [residual]
      nlinarith only [h i, mul_nonneg hc.le (sq_nonneg (y i - q * x i))]
    have hsum : ∑ i, π i * residual i = 0 := by
      have hid : ∑ i, π i * residual i = d * sz - 2 * c * q * sy + c * q ^ 2 * sx := by
        dsimp only [residual, sx, sy, sz]
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hid]
      dsimp only [q]
      field_simp
      nlinarith only [heq]
    refine ⟨q, ?_⟩
    intro i hi
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ ↦ mul_nonneg (hπ i) (hres i))).mp hsum i (Finset.mem_univ i)
    have hrzero : residual i = 0 := (mul_eq_zero.mp hzero).resolve_left hi.ne'
    have hid : d * x i * z i - c * y i ^ 2 + c * (y i - q * x i) ^ 2 = 0 := by
      dsimp only [residual] at hrzero
      nlinarith only [mul_eq_zero_of_left hrzero (x i)]
    have hsquare : (y i - q * x i) ^ 2 = 0 := by
      have : c * (y i - q * x i) ^ 2 = 0 := by
        nlinarith only [hid, h i, mul_nonneg hc.le (sq_nonneg (y i - q * x i))]
      exact (mul_eq_zero.mp this).resolve_left hc.ne'
    constructor
    · rw [hsquare] at hid
      linarith only [hid]
    · nlinarith only [hsquare]
  · rintro ⟨q, hq⟩
    have hsy : sy = q * sx := by
      dsimp only [sy, sx]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      obtain hzero | hpos := (hπ i).eq_or_lt
      · simp [← hzero]
      · rw [(hq i hpos).2]
        ring
    have hsz : d * sz = c * q ^ 2 * sx := by
      dsimp only [sz, sx]
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      obtain hzero | hpos := (hπ i).eq_or_lt
      · simp [← hzero]
      · have hsharp := (hq i hpos).1
        rw [(hq i hpos).2] at hsharp
        have hz : d * z i = c * q ^ 2 * x i := by
          apply (mul_right_cancel₀ (hx i).ne')
          nlinarith only [hsharp]
        calc
          d * (π i * z i) = π i * (d * z i) := by ring
          _ = c * q ^ 2 * (π i * x i) := by rw [hz]; ring
    rw [hsy]
    nlinarith only [congrArg (fun t ↦ sx * t) hsz]

/-- Equality requires sharp components and a common ratio of second to first moments. -/
theorem MomentClass.finite_mixture_third_eq_iff {ι : Type*} [Fintype ι]
    {k : ℝ} (π m1 m2 m3 : ι → ℝ) (hπ : ∀ i, 0 ≤ π i)
    (hx : ∀ i, MomentClass k (m1 i) (m2 i) (m3 i))
    (hmean : 0 < ∑ i, π i * m1 i) :
    (k + 2) * (∑ i, π i * m2 i) ^ 2 =
        (k + 1) * (∑ i, π i * m1 i) * (∑ i, π i * m3 i) ↔
      ∃ q : ℝ, ∀ i, 0 < π i →
        (k + 2) * m2 i ^ 2 = (k + 1) * m1 i * m3 i ∧ m2 i / m1 i = q := by
  have hk : 0 < k := by
    obtain ⟨i, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hmean.ne'
    exact (hx i).parameter_pos
  rw [weighted_quadratic_eq_iff π m1 m2 m3 (by linarith : 0 < k + 2)
    hπ (fun i ↦ (hx i).mean_pos) (fun i ↦ (hx i).third_bound) hmean]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, fun i hi ↦ ⟨(hq i hi).1,
      (div_eq_iff (hx i).mean_pos.ne').mpr (hq i hi).2⟩⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, fun i hi ↦ ⟨(hq i hi).1,
      (div_eq_iff (hx i).mean_pos.ne').mp (hq i hi).2⟩⟩

end SSPRK
