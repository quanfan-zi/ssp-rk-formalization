import SSPRK.MomentMixture
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Fintype.BigOperators

/-!
# Countable mixtures of moment classes

The missing mass is an atom at zero.  Summability of the weights is stated explicitly,
since a real `tsum` alone does not distinguish a divergent series from its default value.
-/

open scoped BigOperators Topology
open Filter

namespace SSPRK

/-- A countable subprobability mixture preserves the first three moment bounds. -/
theorem MomentClass.countable_mixture {k : ℝ} (π x a c : ℕ → ℝ)
    (hπ : ∀ i, 0 ≤ π i) (hπsum : Summable π) (hmass : ∑' i, π i ≤ 1)
    (hx : ∀ i, MomentClass k (x i) (a i) (c i))
    (hsum_x : Summable fun i ↦ π i * x i)
    (hsum_a : Summable fun i ↦ π i * a i)
    (hsum_c : Summable fun i ↦ π i * c i)
    (hmean : 0 < ∑' i, π i * x i) :
    MomentClass k (∑' i, π i * x i) (∑' i, π i * a i)
      (∑' i, π i * c i) := by
  let sx := fun n ↦ ∑ i ∈ Finset.range n, π i * x i
  let sa := fun n ↦ ∑ i ∈ Finset.range n, π i * a i
  let sc := fun n ↦ ∑ i ∈ Finset.range n, π i * c i
  have hsx : Tendsto sx atTop (𝓝 (∑' i, π i * x i)) :=
    hsum_x.hasSum.tendsto_sum_nat
  have hsa : Tendsto sa atTop (𝓝 (∑' i, π i * a i)) :=
    hsum_a.hasSum.tendsto_sum_nat
  have hsc : Tendsto sc atTop (𝓝 (∑' i, π i * c i)) :=
    hsum_c.hasSum.tendsto_sum_nat
  have hsx_pos : ∀ᶠ n in atTop, 0 < sx n :=
    hsx.eventually (eventually_gt_nhds hmean)
  have hfinite (n : ℕ) (hn : 0 < sx n) : MomentClass k (sx n) (sa n) (sc n) := by
    have hmass_n : ∑ i : Fin n, π i ≤ 1 := by
      rw [Fin.sum_univ_eq_sum_range]
      exact (hπsum.sum_le_tsum (Finset.range n) (fun i _ ↦ hπ i)).trans hmass
    have hclass := MomentClass.finite_mixture
      (fun i : Fin n ↦ π i) (fun i : Fin n ↦ x i) (fun i : Fin n ↦ a i)
      (fun i : Fin n ↦ c i) (fun i ↦ hπ i) hmass_n (fun i ↦ hx i) (by
        rw [Fin.sum_univ_eq_sum_range (fun i ↦ π i * x i) n]
        exact hn)
    change MomentClass k (∑ i ∈ Finset.range n, π i * x i)
      (∑ i ∈ Finset.range n, π i * a i) (∑ i ∈ Finset.range n, π i * c i)
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ π i * x i) n] at hclass
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ π i * a i) n] at hclass
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ π i * c i) n] at hclass
    exact hclass
  have hk : 0 < k := (hx 0).parameter_pos
  refine ⟨hk, hmean,
    tsum_nonneg (fun i ↦ mul_nonneg (hπ i) (hx i).second_nonneg),
    tsum_nonneg (fun i ↦ mul_nonneg (hπ i) (hx i).third_nonneg), ?_, ?_⟩
  · apply le_of_tendsto_of_tendsto ((hsx.pow 2).const_mul (k + 1))
      (hsa.const_mul k)
    exact hsx_pos.mono fun n hn ↦ (hfinite n hn).second_bound
  · apply le_of_tendsto_of_tendsto ((hsa.pow 2).const_mul (k + 2))
      ((hsx.const_mul (k + 1)).mul hsc)
    exact hsx_pos.mono fun n hn ↦ (hfinite n hn).third_bound

/-- Equality in the countable third-moment bound is equivalent to sharp supported
components with a common second-to-first moment ratio. -/
theorem MomentClass.countable_mixture_third_eq_iff {k : ℝ} (π x a c : ℕ → ℝ)
    (hπ : ∀ i, 0 ≤ π i) (hx : ∀ i, MomentClass k (x i) (a i) (c i))
    (hsum_x : Summable fun i ↦ π i * x i)
    (hsum_a : Summable fun i ↦ π i * a i)
    (hsum_c : Summable fun i ↦ π i * c i)
    (hmean : 0 < ∑' i, π i * x i) :
    (k + 2) * (∑' i, π i * a i) ^ 2 =
        (k + 1) * (∑' i, π i * x i) * (∑' i, π i * c i) ↔
      ∃ q : ℝ, ∀ i, 0 < π i →
        (k + 2) * a i ^ 2 = (k + 1) * x i * c i ∧ a i / x i = q := by
  let sx := ∑' i, π i * x i
  let sa := ∑' i, π i * a i
  let sc := ∑' i, π i * c i
  have hk : 0 < k := (hx 0).parameter_pos
  change (k + 2) * sa ^ 2 = (k + 1) * sx * sc ↔ _
  constructor
  · intro heq
    let q := sa / sx
    let residual := fun i ↦
      (k + 1) * c i - 2 * (k + 2) * q * a i + (k + 2) * q ^ 2 * x i
    have hres (i : ℕ) : 0 ≤ residual i := by
      apply nonneg_of_mul_nonneg_left (b := x i) ?_ (hx i).mean_pos
      dsimp only [residual]
      nlinarith only [(hx i).third_bound,
        mul_nonneg (by linarith : 0 ≤ k + 2) (sq_nonneg (a i - q * x i))]
    have hsum_res : Summable fun i ↦ π i * residual i := by
      refine ((hsum_c.mul_left (k + 1)).add
        ((hsum_a.mul_left (-2 * (k + 2) * q)).add
          (hsum_x.mul_left ((k + 2) * q ^ 2)))).congr ?_
      intro i
      dsimp only [residual]
      ring
    have htsum_res : ∑' i, π i * residual i =
        (k + 1) * sc - 2 * (k + 2) * q * sa + (k + 2) * q ^ 2 * sx := by
      calc
        ∑' i, π i * residual i = ∑' i, (
            (k + 1) * (π i * c i) +
              ((-2 * (k + 2) * q) * (π i * a i) +
                ((k + 2) * q ^ 2) * (π i * x i))) := by
          apply tsum_congr
          intro i
          dsimp only [residual]
          ring
        _ = (∑' i, (k + 1) * (π i * c i)) +
            ∑' i, ((-2 * (k + 2) * q) * (π i * a i) +
              ((k + 2) * q ^ 2) * (π i * x i)) := by
          rw [(hsum_c.mul_left (k + 1)).tsum_add
            ((hsum_a.mul_left (-2 * (k + 2) * q)).add
              (hsum_x.mul_left ((k + 2) * q ^ 2)))]
        _ = (∑' i, (k + 1) * (π i * c i)) +
            (∑' i, (-2 * (k + 2) * q) * (π i * a i)) +
              ∑' i, ((k + 2) * q ^ 2) * (π i * x i) := by
          rw [(hsum_a.mul_left (-2 * (k + 2) * q)).tsum_add
            (hsum_x.mul_left ((k + 2) * q ^ 2))]
          ring
        _ = (k + 1) * sc - 2 * (k + 2) * q * sa +
            (k + 2) * q ^ 2 * sx := by
          simp only [tsum_mul_left]
          dsimp only [sx, sa, sc]
          ring
    have hzero : ∑' i, π i * residual i = 0 := by
      rw [htsum_res]
      have hsc_formula : (k + 1) * sc = (k + 2) * sa ^ 2 / sx := by
        apply (eq_div_iff hmean.ne').mpr
        nlinarith only [heq]
      rw [hsc_formula]
      dsimp only [q]
      field_simp [hmean.ne']
      ring
    refine ⟨q, fun i hi ↦ ?_⟩
    have hterm_le : π i * residual i ≤ ∑' j, π j * residual j :=
      by simpa only [Finset.sum_singleton] using
        hsum_res.sum_le_tsum {i} (fun j _ ↦ mul_nonneg (hπ j) (hres j))
    have hterm : π i * residual i = 0 := by
      apply le_antisymm
      · simpa only [hzero] using hterm_le
      · exact mul_nonneg (hπ i) (hres i)
    have hrzero : residual i = 0 := (mul_eq_zero.mp hterm).resolve_left hi.ne'
    have hid : (k + 1) * x i * c i - (k + 2) * a i ^ 2 +
        (k + 2) * (a i - q * x i) ^ 2 = 0 := by
      dsimp only [residual] at hrzero
      nlinarith only [mul_eq_zero_of_left hrzero (x i)]
    have hsquare : (a i - q * x i) ^ 2 = 0 := by
      have hz : (k + 2) * (a i - q * x i) ^ 2 = 0 := by
        nlinarith only [hid, (hx i).third_bound,
          mul_nonneg (by linarith : 0 ≤ k + 2) (sq_nonneg (a i - q * x i))]
      exact (mul_eq_zero.mp hz).resolve_left (by linarith)
    constructor
    · rw [hsquare] at hid
      linarith only [hid]
    · apply (div_eq_iff (hx i).mean_pos.ne').mpr
      nlinarith only [hsquare]
  · rintro ⟨q, hq⟩
    have hsa_eq : sa = q * sx := by
      calc
        sa = ∑' i, q * (π i * x i) := by
          apply tsum_congr
          intro i
          obtain hzero | hpos := (hπ i).eq_or_lt
          · simp [← hzero]
          · have hratio := (div_eq_iff (hx i).mean_pos.ne').mp (hq i hpos).2
            rw [hratio]
            ring
        _ = q * sx := tsum_mul_left
    have hsc_eq : (k + 1) * sc = (k + 2) * q ^ 2 * sx := by
      calc
        (k + 1) * sc = ∑' i, (k + 1) * (π i * c i) := by
          rw [tsum_mul_left]
        _ = ∑' i, ((k + 2) * q ^ 2) * (π i * x i) := by
          apply tsum_congr
          intro i
          obtain hzero | hpos := (hπ i).eq_or_lt
          · simp [← hzero]
          · have hratio :=
              (div_eq_iff (hx i).mean_pos.ne').mp (hq i hpos).2
            have hsharp := (hq i hpos).1
            have hc_eq : (k + 1) * c i = (k + 2) * q ^ 2 * x i := by
              apply mul_left_cancel₀ (hx i).mean_pos.ne'
              calc
                x i * ((k + 1) * c i) = (k + 1) * x i * c i := by ring
                _ = (k + 2) * a i ^ 2 := hsharp.symm
                _ = x i * ((k + 2) * q ^ 2 * x i) := by rw [hratio]; ring
            calc
              (k + 1) * (π i * c i) = π i * ((k + 1) * c i) := by ring
              _ = ((k + 2) * q ^ 2) * (π i * x i) := by rw [hc_eq]; ring
        _ = (k + 2) * q ^ 2 * sx := tsum_mul_left
    rw [hsa_eq]
    calc
      (k + 2) * (q * sx) ^ 2 = ((k + 2) * q ^ 2 * sx) * sx := by ring
      _ = ((k + 1) * sc) * sx := by rw [hsc_eq]
      _ = (k + 1) * sx * sc := by ring

end SSPRK
