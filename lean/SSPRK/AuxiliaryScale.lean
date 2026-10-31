import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# A two-point auxiliary scale

The real-algebraic construction realizes the prescribed first three
moments using two nonnegative scale values. No probability measure is defined here.
-/

namespace SSPRK

private lemma auxiliary_scale_roots {a b η : ℝ} (hη : 0 < η) (hb : 0 ≤ b)
    (ha : a = 1 + η + b) :
    ∃ lo hi : ℝ, 0 ≤ lo ∧ lo < 1 ∧ 1 < hi ∧
      lo ^ 2 = a * lo - b ∧ hi ^ 2 = a * hi - b := by
  have hdisc : 0 < a ^ 2 - 4 * b := by nlinarith [sq_nonneg (a - 2)]
  let z := Real.sqrt (a ^ 2 - 4 * b)
  have hz : 0 ≤ z := Real.sqrt_nonneg _
  have hzsq : z ^ 2 = a ^ 2 - 4 * b := Real.sq_sqrt hdisc.le
  have haz : z ≤ a := by nlinarith
  have hlt : (a - 2) ^ 2 < z ^ 2 := by nlinarith
  have habs : |a - 2| < z := by
    exact (sq_lt_sq₀ (abs_nonneg _) hz).mp (by simpa only [sq_abs] using hlt)
  obtain ⟨hleft, hright⟩ := abs_lt.mp habs
  refine ⟨(a - z) / 2, (a + z) / 2, by linarith, by linarith, by linarith, ?_, ?_⟩
  · nlinarith
  · nlinarith

theorem exists_auxiliary_scale_of_pos (η1 η2 : ℝ) (hη1 : 0 < η1) (hη2 : 0 ≤ η2) :
    ∃ lo hi p q : ℝ, 0 ≤ lo ∧ lo < 1 ∧ 1 < hi ∧ 0 < p ∧ 0 < q ∧
      p + q = 1 ∧ p * lo + q * hi = 1 ∧
      p * lo ^ 2 + q * hi ^ 2 = 1 + η1 ∧
      p * lo ^ 3 + q * hi ^ 3 = (1 + η1) ^ 2 + η2 / 2 := by
  let b : ℝ := η2 / (2 * η1)
  let a : ℝ := 1 + η1 + b
  have hb : 0 ≤ b := div_nonneg hη2 (by positivity)
  obtain ⟨lo, hi, hlo, hlo1, hhi1, hloroot, hhiroot⟩ :=
    auxiliary_scale_roots hη1 hb (show a = 1 + η1 + b from rfl)
  let p : ℝ := (hi - 1) / (hi - lo)
  let q : ℝ := (1 - lo) / (hi - lo)
  have hdenpos : 0 < hi - lo := by linarith
  have hden : hi - lo ≠ 0 := ne_of_gt hdenpos
  have hp : 0 < p := div_pos (by linarith) hdenpos
  have hq : 0 < q := div_pos (by linarith) hdenpos
  have hsum : p + q = 1 := by
    dsimp [p, q]
    field_simp [hden]; ring
  have hmean : p * lo + q * hi = 1 := by
    dsimp [p, q]
    field_simp [hden]; ring
  have hsecond : p * lo ^ 2 + q * hi ^ 2 = a - b := by
    rw [hloroot, hhiroot]
    calc
      _ = a * (p * lo + q * hi) - b * (p + q) := by ring
      _ = _ := by rw [hmean, hsum]; ring
  have hlo3 : lo ^ 3 = a * lo ^ 2 - b * lo := by
    nlinarith only [congrArg (fun z : ℝ ↦ z * lo) hloroot]
  have hhi3 : hi ^ 3 = a * hi ^ 2 - b * hi := by
    nlinarith only [congrArg (fun z : ℝ ↦ z * hi) hhiroot]
  have hthird : p * lo ^ 3 + q * hi ^ 3 = a * (a - b) - b := by
    rw [hlo3, hhi3]
    calc
      _ = a * (p * lo ^ 2 + q * hi ^ 2) - b * (p * lo + q * hi) := by ring
      _ = _ := by rw [hsecond, hmean]; ring
  refine ⟨lo, hi, p, q, hlo, hlo1, hhi1, hp, hq, hsum, hmean, ?_, ?_⟩
  · simpa only [a, add_sub_cancel_right] using hsecond
  · rw [hthird]
    dsimp [a, b]
    field_simp; ring

/-- Nonnegative two-point scales realize the prescribed three auxiliary moments. -/
theorem exists_auxiliary_scale (η1 η2 : ℝ) (hη1 : 0 ≤ η1) (hη2 : 0 ≤ η2)
    (hzero : η1 = 0 → η2 = 0) :
    ∃ lo hi p q : ℝ, 0 ≤ lo ∧ 0 ≤ hi ∧ 0 ≤ p ∧ 0 ≤ q ∧
      p + q = 1 ∧ p * lo + q * hi = 1 ∧
      p * lo ^ 2 + q * hi ^ 2 = 1 + η1 ∧
      p * lo ^ 3 + q * hi ^ 3 = (1 + η1) ^ 2 + η2 / 2 := by
  by_cases hz : η1 = 0
  · have hz2 := hzero hz
    refine ⟨1, 1, 1, 0, ?_⟩
    simp [hz, hz2]
  · obtain ⟨lo, hi, p, q, hlo, hlo1, hhi1, hp, hq, hsum, hmean, hsecond, hthird⟩ :=
      exists_auxiliary_scale_of_pos η1 η2 (lt_of_le_of_ne hη1 (Ne.symm hz)) hη2
    exact ⟨lo, hi, p, q, hlo, by linarith, hp.le, hq.le, hsum, hmean, hsecond, hthird⟩

end SSPRK
