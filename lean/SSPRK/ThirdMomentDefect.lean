import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import SSPRK.MomentAlgebra

/-!
# The exact third-moment defect in V2.10

The scalar identities in the paper's nonnegative-decomposition argument. The variables
`x`, `y`, `z` are the first three moments of the deleted occupation time; `a`, `b` are
the two nonnegative return corrections. These identities do not assert independence.
-/

namespace SSPRK

noncomputable section

/-- The adjacent third-moment defect at phase count `s`. -/
def thirdMomentDefect (s m₁ m₂ m₃ : ℝ) : ℝ :=
  m₁ * m₃ - (s + 2) / (s + 1) * m₂ ^ 2

/-- The remainder after subtracting the smaller PH defect and the second return term. -/
def thirdMomentRemainder (s x y a : ℝ) : ℝ :=
  (1 + x) * (6 + 6 * x + 3 * y + (s + 1) / s * (y ^ 2 / x) +
    6 * (x + 2) * a + 6 * a ^ 2) -
    (s + 2) / (s + 1) * (2 + 2 * x + y + 2 * a) ^ 2

/-- Deviation of the deleted mean from the unit-rate Erlang mean. -/
def erlangMeanDefect (s x : ℝ) : ℝ := x / (s - 1) - 1

/-- Deviation of the deleted second moment from its minimum-variance value. -/
def erlangVarianceDefect (s x y : ℝ) : ℝ := y / x - s / (s - 1) * x

/-- The six squares and two nonnegative terms in the paper's remainder certificate. -/
def thirdMomentSquares (s x a u v : ℝ) : ℝ :=
  2 * (s - 1) * (a - u) ^ 2 + x ^ 2 / s * (v + s * u) ^ 2 +
  x / s * v ^ 2 + x * (s + 2) * (v - 2 * a + u) ^ 2 +
  2 * (s - 1) * x * a ^ 2 + x * (3 * s - 2) * u ^ 2 +
  x / (s - 1) * ((s ^ 2 + 1) * x + (s - 1) ^ 2) * v +
  2 * x * ((s - 1) * x + 3 * s - 1) * a

/-- Equation `exactdefect`: the original defect splits into three terms. -/
theorem thirdMomentDefect_decomposition (s x y z a b : ℝ) (hx : x ≠ 0) :
    thirdMomentDefect s (1 + x) (2 + 2 * x + y + 2 * a)
      (6 + 6 * x + 3 * y + z + 6 * (x + 2) * a + 6 * a ^ 2 + 3 * b) =
    (1 + x) / x * (x * z - (s + 1) / s * y ^ 2) +
      3 * (1 + x) * b + thirdMomentRemainder s x y a := by
  unfold thirdMomentDefect thirdMomentRemainder
  field_simp [hx]
  ring

/-- Equation `gsos`: the paper's exact six-square certificate. -/
theorem thirdMomentRemainder_squares (s x y a : ℝ)
    (hs : s ≠ 0) (hs₁ : s - 1 ≠ 0) (hs₂ : s + 1 ≠ 0) (hx : x ≠ 0) :
    (s + 1) * thirdMomentRemainder s x y a =
      thirdMomentSquares s x a (erlangMeanDefect s x) (erlangVarianceDefect s x y) := by
  unfold thirdMomentRemainder thirdMomentSquares erlangMeanDefect erlangVarianceDefect
  field_simp [hs, hs₁, hs₂, hx]
  ring

/-- Every coefficient in the remainder certificate is positive in the induction case. -/
theorem thirdMomentSquares_nonneg {s x a u v : ℝ}
    (hs : 1 < s) (hx : 0 < x) (ha : 0 ≤ a) (hv : 0 ≤ v) :
    0 ≤ thirdMomentSquares s x a u v := by
  have hs₀ : 0 < s := lt_trans zero_lt_one hs
  have hs₁ : 0 < s - 1 := sub_pos.mpr hs
  have hs₃ : 0 < 3 * s - 2 := by linarith
  have hlast : 0 ≤ (s - 1) * x + 3 * s - 1 := by
    nlinarith [mul_nonneg hs₁.le hx.le]
  unfold thirdMomentSquares
  positivity

/-- The variance bound for the smaller PH law makes the variance defect nonnegative. -/
theorem erlangVarianceDefect_nonneg {s x y : ℝ} (hx : 0 < x)
    (hy : s / (s - 1) * x ^ 2 ≤ y) : 0 ≤ erlangVarianceDefect s x y := by
  unfold erlangVarianceDefect
  apply sub_nonneg.mpr
  apply (le_div_iff₀ hx).mpr
  nlinarith only [hy]

/-- The paper's remainder is nonnegative, by its explicit sum-of-squares identity. -/
theorem thirdMomentRemainder_nonneg {s x y a : ℝ}
    (hs : 1 < s) (hx : 0 < x) (ha : 0 ≤ a)
    (hy : s / (s - 1) * x ^ 2 ≤ y) : 0 ≤ thirdMomentRemainder s x y a := by
  have hs₀ : 0 < s := lt_trans zero_lt_one hs
  have hs₁ : 0 < s - 1 := sub_pos.mpr hs
  have hs₂ : 0 < s + 1 := by linarith
  apply nonneg_of_mul_nonneg_left (b := s + 1) _ hs₂
  rw [mul_comm]
  rw [thirdMomentRemainder_squares s x y a hs₀.ne' hs₁.ne' hs₂.ne' hx.ne']
  exact thirdMomentSquares_nonneg hs hx ha (erlangVarianceDefect_nonneg hx hy)

/-- The induction step for the third-moment defect, with no independent replacement law. -/
theorem thirdMomentDefect_nonneg {s x y z a b : ℝ}
    (hs : 1 < s) (hx : 0 < x) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hy : s / (s - 1) * x ^ 2 ≤ y)
    (hz : (s + 1) / s * y ^ 2 ≤ x * z) :
    0 ≤ thirdMomentDefect s (1 + x) (2 + 2 * x + y + 2 * a)
      (6 + 6 * x + 3 * y + z + 6 * (x + 2) * a + 6 * a ^ 2 + 3 * b) := by
  rw [thirdMomentDefect_decomposition s x y z a b hx.ne']
  exact add_nonneg (add_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hz))
    (mul_nonneg (by positivity) hb)) (thirdMomentRemainder_nonneg hs hx ha hy)

/-- Vanishing of the certificate forces the mean, variance, and return deviations to vanish. -/
theorem thirdMomentSquares_eq_zero {s x a u v : ℝ}
    (hs : 1 < s) (hx : 0 < x) (ha : 0 ≤ a) (hv : 0 ≤ v)
    (heq : thirdMomentSquares s x a u v = 0) : u = 0 ∧ v = 0 ∧ a = 0 := by
  have hs₀ : 0 < s := lt_trans zero_lt_one hs
  have hs₁ : 0 < s - 1 := sub_pos.mpr hs
  have hs₃ : 0 < 3 * s - 2 := by linarith
  have hlast : 0 ≤ (s - 1) * x + 3 * s - 1 := by
    nlinarith [mul_nonneg hs₁.le hx.le]
  have h₁ : 0 ≤ 2 * (s - 1) * (a - u) ^ 2 := by positivity
  have h₂ : 0 ≤ x ^ 2 / s * (v + s * u) ^ 2 := by positivity
  have h₃ : 0 ≤ x / s * v ^ 2 := by positivity
  have h₄ : 0 ≤ x * (s + 2) * (v - 2 * a + u) ^ 2 := by positivity
  have h₅ : 0 ≤ 2 * (s - 1) * x * a ^ 2 := by positivity
  have h₆ : 0 ≤ x * (3 * s - 2) * u ^ 2 := by positivity
  have h₇ : 0 ≤ x / (s - 1) * ((s ^ 2 + 1) * x + (s - 1) ^ 2) * v := by positivity
  have h₈ : 0 ≤ 2 * x * ((s - 1) * x + 3 * s - 1) * a := by positivity
  unfold thirdMomentSquares at heq
  have hu : x * (3 * s - 2) * u ^ 2 = 0 := by
    linarith only [heq, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈]
  have hv' : x / s * v ^ 2 = 0 := by
    linarith only [heq, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈]
  have ha' : 2 * (s - 1) * x * a ^ 2 = 0 := by
    linarith only [heq, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈]
  exact ⟨sq_eq_zero_iff.mp ((mul_eq_zero.mp hu).resolve_left (mul_pos hx hs₃).ne'),
    sq_eq_zero_iff.mp ((mul_eq_zero.mp hv').resolve_left (div_pos hx hs₀).ne'),
    sq_eq_zero_iff.mp ((mul_eq_zero.mp ha').resolve_left (by positivity))⟩

/-- Equality in the induction step forces exactly the four parameters stated in V2.10. -/
theorem thirdMomentDefect_equality_parameters {s x y z a b : ℝ}
    (hs : 1 < s) (hx : 0 < x) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hy : s / (s - 1) * x ^ 2 ≤ y)
    (hz : (s + 1) / s * y ^ 2 ≤ x * z)
    (heq : thirdMomentDefect s (1 + x) (2 + 2 * x + y + 2 * a)
      (6 + 6 * x + 3 * y + z + 6 * (x + 2) * a + 6 * a ^ 2 + 3 * b) = 0) :
    x = s - 1 ∧ y = s * (s - 1) ∧ a = 0 ∧ b = 0 := by
  have hs₀ : 0 < s := lt_trans zero_lt_one hs
  have hs₁ : 0 < s - 1 := sub_pos.mpr hs
  have hs₂ : 0 < s + 1 := by linarith
  have hind : 0 ≤ (1 + x) / x * (x * z - (s + 1) / s * y ^ 2) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hz)
  have hreturn : 0 ≤ 3 * (1 + x) * b := mul_nonneg (by positivity) hb
  have hrem := thirdMomentRemainder_nonneg hs hx ha hy
  rw [thirdMomentDefect_decomposition s x y z a b hx.ne'] at heq
  have hremzero : thirdMomentRemainder s x y a = 0 := by
    linarith only [heq, hind, hreturn, hrem]
  have hreturnzero : 3 * (1 + x) * b = 0 := by
    linarith only [heq, hind, hreturn, hrem]
  have hsquares : thirdMomentSquares s x a (erlangMeanDefect s x)
      (erlangVarianceDefect s x y) = 0 := by
    rw [← thirdMomentRemainder_squares s x y a hs₀.ne' hs₁.ne' hs₂.ne' hx.ne',
      hremzero, mul_zero]
  obtain ⟨hu, hv, ha'⟩ := thirdMomentSquares_eq_zero hs hx ha
    (erlangVarianceDefect_nonneg hx hy) hsquares
  have hx' : x = s - 1 :=
    (div_eq_one_iff_eq hs₁.ne').mp (sub_eq_zero.mp hu)
  have hy' : y = s * (s - 1) := by
    apply (div_eq_iff hs₁.ne').mp
    have h := sub_eq_zero.mp hv
    simpa only [hx', div_mul_cancel₀ _ hs₁.ne'] using h
  exact ⟨hx', hy', ha', (mul_eq_zero.mp hreturnzero).resolve_left (by positivity)⟩

/-- The moment-class induction step proved by the V2.10 defect certificate. -/
theorem MomentClass.block_defect {n x y z a b : ℝ} (h : MomentClass n x y z)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    MomentClass (n + 1) (1 + x) (2 + 2 * x + y + 2 * a)
      (6 + 6 * x + 3 * y + z + 6 * (x + 2) * a + 6 * a ^ 2 + 3 * b) := by
  have hn := h.parameter_pos
  have hx := h.mean_pos
  have hy := h.second_nonneg
  have hz := h.third_nonneg
  have hn₁ : 0 < n + 1 := by positivity
  have hsecond := second_moment_add n 1 x 1 y (2 * (1 + a)) hn (by norm_num)
    h.second_bound (by nlinarith only [ha])
  have hybound : (n + 1) / n * x ^ 2 ≤ y := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hn).mpr (by nlinarith only [h.second_bound])
  have hzbound : (n + 2) / (n + 1) * y ^ 2 ≤ x * z := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hn₁).mpr (by nlinarith only [h.third_bound])
  have hdef := thirdMomentDefect_nonneg (s := n + 1) (by linarith) hx ha hb
    (by simpa using hybound) (by convert hzbound using 1; ring)
  refine ⟨hn₁, by positivity, by positivity, by positivity, ?_, ?_⟩
  · nlinarith only [hsecond]
  · unfold thirdMomentDefect at hdef
    have h := (div_le_iff₀ (show 0 < n + 1 + 1 by positivity)).mp
      (show (n + 1 + 2) * (2 + 2 * x + y + 2 * a) ^ 2 / (n + 1 + 1) ≤
          (1 + x) *
            (6 + 6 * x + 3 * y + z + 6 * (x + 2) * a + 6 * a ^ 2 + 3 * b) by
        simpa only [div_mul_eq_mul_div] using sub_nonneg.mp hdef)
    nlinarith only [h]

/-- Equality for a moment-class block forces the normalized Erlang parameters. -/
theorem MomentClass.block_defect_eq_parameters {n x y z a b : ℝ} (h : MomentClass n x y z)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (heq : (n + 3) * (2 + 2 * x + y + 2 * a) ^ 2 =
      (n + 2) * (1 + x) *
        (6 + 6 * x + 3 * y + z + 6 * (x + 2) * a + 6 * a ^ 2 + 3 * b)) :
    x = n ∧ y = (n + 1) * n ∧ a = 0 ∧ b = 0 := by
  have hn := h.parameter_pos
  have hn₁ : 0 < n + 1 := by positivity
  have hybound : (n + 1) / n * x ^ 2 ≤ y := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hn).mpr (by nlinarith only [h.second_bound])
  have hzbound : (n + 2) / (n + 1) * y ^ 2 ≤ x * z := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hn₁).mpr (by nlinarith only [h.third_bound])
  have hzero : thirdMomentDefect (n + 1) (1 + x) (2 + 2 * x + y + 2 * a)
      (6 + 6 * x + 3 * y + z + 6 * (x + 2) * a + 6 * a ^ 2 + 3 * b) = 0 := by
    unfold thirdMomentDefect
    apply sub_eq_zero.mpr
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff (by positivity : n + 1 + 1 ≠ 0)).mpr
    nlinarith only [heq]
  have hresult := thirdMomentDefect_equality_parameters (s := n + 1)
    (by linarith) h.mean_pos ha hb (by simpa using hybound)
    (by convert hzbound using 1; ring) hzero
  simpa only [add_sub_cancel_right] using hresult

end

end SSPRK
