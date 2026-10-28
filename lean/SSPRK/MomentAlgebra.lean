import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Algebra of the first three moments

Moment classes and their closure under the moment convolution of independent sums.
The proof uses polynomial certificates for
the variance comparison and the two-component length-biased mixture.
-/

namespace SSPRK

/-- The first three moments satisfy the two inequalities defining the class `C_k`. -/
structure MomentClass (k m1 m2 m3 : ℝ) : Prop where
  parameter_pos : 0 < k
  mean_pos : 0 < m1
  second_nonneg : 0 ≤ m2
  third_nonneg : 0 ≤ m3
  second_bound : (k + 1) * m1 ^ 2 ≤ k * m2
  third_bound : (k + 2) * m2 ^ 2 ≤ (k + 1) * m1 * m3

/-- The ordinary second-moment inequality is closed under independent sums. -/
lemma second_moment_add (p q x y a b : ℝ) (hp : 0 < p) (hq : 0 < q)
    (ha : (p + 1) * x ^ 2 ≤ p * a) (hb : (q + 1) * y ^ 2 ≤ q * b) :
    (p + q + 1) * (x + y) ^ 2 ≤ (p + q) * (a + b + 2 * x * y) := by
  have certificate :
      p * q * ((p + q) * (a + b + 2 * x * y) - (p + q + 1) * (x + y) ^ 2) =
        q * (p + q) * (p * a - (p + 1) * x ^ 2) +
        p * (p + q) * (q * b - (q + 1) * y ^ 2) + (q * x - p * y) ^ 2 := by ring
  have hnonneg : 0 ≤ p * q *
      ((p + q) * (a + b + 2 * x * y) - (p + q + 1) * (x + y) ^ 2) := by
    rw [certificate]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg (mul_nonneg hq.le (add_pos hp hq).le) (sub_nonneg.mpr ha))
        (mul_nonneg (mul_nonneg hp.le (add_pos hp hq).le) (sub_nonneg.mpr hb)))
      (sq_nonneg _)
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hnonneg (mul_pos hp hq))

/-- A common second-moment bound is preserved by a mixture with positive masses. -/
lemma second_moment_mix (k x y u v c d : ℝ) (hk : 0 ≤ k + 1)
    (hx : 0 < x) (hy : 0 < y)
    (hc : (k + 1) * u ^ 2 ≤ k * x * c)
    (hd : (k + 1) * v ^ 2 ≤ k * y * d) :
    (k + 1) * (u + v) ^ 2 ≤ k * (x + y) * (c + d) := by
  have certificate :
      x * y * (k * (x + y) * (c + d) - (k + 1) * (u + v) ^ 2) =
        y * (x + y) * (k * x * c - (k + 1) * u ^ 2) +
        x * (x + y) * (k * y * d - (k + 1) * v ^ 2) +
        (k + 1) * (y * u - x * v) ^ 2 := by ring
  have hnonneg : 0 ≤ x * y *
      (k * (x + y) * (c + d) - (k + 1) * (u + v) ^ 2) := by
    rw [certificate]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg (mul_nonneg hy.le (add_pos hx hy).le) (sub_nonneg.mpr hc))
        (mul_nonneg (mul_nonneg hx.le (add_pos hx hy).le) (sub_nonneg.mpr hd)))
      (mul_nonneg hk (sq_nonneg _))
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hnonneg (mul_pos hx hy))

/-- Clear the mean denominator in the first length-biased component of a sum. -/
lemma length_biased_component_bound (p q x y a b c : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hc : (p + 2) * a ^ 2 ≤ (p + 1) * x * c)
    (hb : (q + 1) * y ^ 2 ≤ q * b) :
    (p + q + 2) * (a + x * y) ^ 2 ≤
      (p + q + 1) * x * (c + x * b + 2 * a * y) := by
  have hb' : (q + 1) * (x * y) ^ 2 ≤ q * (x ^ 2 * b) := by
    nlinarith only [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hb)]
  have h := second_moment_add (p + 1) q a (x * y) (x * c) (x ^ 2 * b)
    (by linarith) hq (by nlinarith only [hc]) hb'
  nlinarith only [h]

/-- The third-moment inequality for independent sums, proved by length-biased mixing. -/
lemma third_moment_add (p q x y a b c d : ℝ)
    (hx : MomentClass p x a c) (hy : MomentClass q y b d) :
    (p + q + 2) * (a + b + 2 * x * y) ^ 2 ≤
      (p + q + 1) * (x + y) * (c + d + 3 * a * y + 3 * x * b) := by
  have hfirst := length_biased_component_bound p q x y a b c
    hx.parameter_pos hy.parameter_pos hx.third_bound hy.second_bound
  have hsecond := length_biased_component_bound q p y x b a d
    hy.parameter_pos hx.parameter_pos hy.third_bound hx.second_bound
  have hmix := second_moment_mix (p + q + 1) x y (a + x * y) (b + y * x)
    (c + x * b + 2 * a * y) (d + y * a + 2 * b * x)
    (by linarith [hx.parameter_pos, hy.parameter_pos]) hx.mean_pos hy.mean_pos
    (by nlinarith only [hfirst]) (by nlinarith only [hsecond])
  nlinarith only [hmix]

/-- Moment convolution adds the class parameters. -/
theorem MomentClass.add {p q x y a b c d : ℝ}
    (hx : MomentClass p x a c) (hy : MomentClass q y b d) :
    MomentClass (p + q) (x + y) (a + b + 2 * x * y)
      (c + d + 3 * a * y + 3 * x * b) := by
  refine ⟨add_pos hx.parameter_pos hy.parameter_pos, add_pos hx.mean_pos hy.mean_pos,
    ?_, ?_, second_moment_add p q x y a b hx.parameter_pos hy.parameter_pos
      hx.second_bound hy.second_bound, third_moment_add p q x y a b c d hx hy⟩
  all_goals positivity [hx.second_nonneg, hy.second_nonneg, hx.third_nonneg,
    hy.third_nonneg, hx.mean_pos, hy.mean_pos]

end SSPRK
