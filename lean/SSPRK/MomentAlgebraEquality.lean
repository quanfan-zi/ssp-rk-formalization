import SSPRK.MomentAlgebra
import Mathlib.Tactic

/-!
# Equality in third-moment convolution

The nonnegative certificates for second-moment convolution and length-biased mixing
identify the necessary equality conditions for convolution.
-/

namespace SSPRK

lemma second_moment_add_eq_conditions (p q x y a b : ℝ) (hp : 0 < p) (hq : 0 < q)
    (ha : (p + 1) * x ^ 2 ≤ p * a) (hb : (q + 1) * y ^ 2 ≤ q * b)
    (he : (p + q + 1) * (x + y) ^ 2 = (p + q) * (a + b + 2 * x * y)) :
    (p + 1) * x ^ 2 = p * a ∧ (q + 1) * y ^ 2 = q * b ∧ q * x = p * y := by
  have hc :
      p * q * ((p + q) * (a + b + 2 * x * y) - (p + q + 1) * (x + y) ^ 2) =
        q * (p + q) * (p * a - (p + 1) * x ^ 2) +
        p * (p + q) * (q * b - (q + 1) * y ^ 2) + (q * x - p * y) ^ 2 := by ring
  have hzero : q * (p + q) * (p * a - (p + 1) * x ^ 2) +
      p * (p + q) * (q * b - (q + 1) * y ^ 2) + (q * x - p * y) ^ 2 = 0 := by
    rw [← hc, ← he, sub_self, mul_zero]
  have hfirst := mul_nonneg (mul_pos hq (add_pos hp hq)).le (sub_nonneg.mpr ha)
  have hsecond := mul_nonneg (mul_pos hp (add_pos hp hq)).le (sub_nonneg.mpr hb)
  have hthird := sq_nonneg (q * x - p * y)
  have hfirst0 : q * (p + q) * (p * a - (p + 1) * x ^ 2) = 0 := by linarith
  have hsecond0 : p * (p + q) * (q * b - (q + 1) * y ^ 2) = 0 := by linarith
  have hthird0 : (q * x - p * y) ^ 2 = 0 := by linarith
  have hfirst' := (mul_eq_zero.mp hfirst0).resolve_left
    (ne_of_gt (mul_pos hq (add_pos hp hq)))
  have hsecond' := (mul_eq_zero.mp hsecond0).resolve_left
    (ne_of_gt (mul_pos hp (add_pos hp hq)))
  exact ⟨(sub_eq_zero.mp hfirst').symm, (sub_eq_zero.mp hsecond').symm,
    sub_eq_zero.mp (sq_eq_zero_iff.mp hthird0)⟩

lemma second_moment_mix_eq_components (k x y u v c d : ℝ) (hk : 0 ≤ k + 1)
    (hx : 0 < x) (hy : 0 < y)
    (hc : (k + 1) * u ^ 2 ≤ k * x * c)
    (hd : (k + 1) * v ^ 2 ≤ k * y * d)
    (he : (k + 1) * (u + v) ^ 2 = k * (x + y) * (c + d)) :
    (k + 1) * u ^ 2 = k * x * c ∧ (k + 1) * v ^ 2 = k * y * d := by
  have hcertificate :
      x * y * (k * (x + y) * (c + d) - (k + 1) * (u + v) ^ 2) =
        y * (x + y) * (k * x * c - (k + 1) * u ^ 2) +
        x * (x + y) * (k * y * d - (k + 1) * v ^ 2) +
        (k + 1) * (y * u - x * v) ^ 2 := by ring
  have hzero : y * (x + y) * (k * x * c - (k + 1) * u ^ 2) +
      x * (x + y) * (k * y * d - (k + 1) * v ^ 2) +
      (k + 1) * (y * u - x * v) ^ 2 = 0 := by
    rw [← hcertificate, ← he, sub_self, mul_zero]
  have hfirst := mul_nonneg (mul_pos hy (add_pos hx hy)).le (sub_nonneg.mpr hc)
  have hsecond := mul_nonneg (mul_pos hx (add_pos hx hy)).le (sub_nonneg.mpr hd)
  have hthird := mul_nonneg hk (sq_nonneg (y * u - x * v))
  have hfirst0 : y * (x + y) * (k * x * c - (k + 1) * u ^ 2) = 0 := by linarith
  have hsecond0 : x * (x + y) * (k * y * d - (k + 1) * v ^ 2) = 0 := by linarith
  have hfirst' := (mul_eq_zero.mp hfirst0).resolve_left
    (ne_of_gt (mul_pos hy (add_pos hx hy)))
  have hsecond' := (mul_eq_zero.mp hsecond0).resolve_left
    (ne_of_gt (mul_pos hx (add_pos hx hy)))
  exact ⟨(sub_eq_zero.mp hfirst').symm, (sub_eq_zero.mp hsecond').symm⟩

lemma length_biased_component_eq_conditions (p q x y a b c : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hx : 0 < x)
    (hc : (p + 2) * a ^ 2 ≤ (p + 1) * x * c)
    (hb : (q + 1) * y ^ 2 ≤ q * b)
    (he : (p + q + 2) * (a + x * y) ^ 2 =
      (p + q + 1) * x * (c + x * b + 2 * a * y)) :
    (q + 1) * y ^ 2 = q * b ∧ q * a = (p + 1) * x * y := by
  have hb' : (q + 1) * (x * y) ^ 2 ≤ q * (x ^ 2 * b) := by
    nlinarith only [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hb)]
  have h := second_moment_add_eq_conditions (p + 1) q a (x * y) (x * c) (x ^ 2 * b)
    (by linarith) hq (by nlinarith only [hc]) hb' (by nlinarith only [he])
  refine ⟨?_, by simpa only [mul_assoc] using h.2.2⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt hx))
  nlinarith only [h.2.1]

theorem third_moment_add_eq_conditions {p q x y a b c d : ℝ}
    (hx : MomentClass p x a c) (hy : MomentClass q y b d)
    (he : (p + q + 2) * (a + b + 2 * x * y) ^ 2 =
      (p + q + 1) * (x + y) * (c + d + 3 * a * y + 3 * x * b)) :
    (p + 1) * x ^ 2 = p * a ∧ (q + 1) * y ^ 2 = q * b ∧ x / p = y / q := by
  have hfirst := length_biased_component_bound p q x y a b c
    hx.parameter_pos hy.parameter_pos hx.third_bound hy.second_bound
  have hsecond := length_biased_component_bound q p y x b a d
    hy.parameter_pos hx.parameter_pos hy.third_bound hx.second_bound
  have hmix := second_moment_mix_eq_components (p + q + 1) x y (a + x * y) (b + y * x)
    (c + x * b + 2 * a * y) (d + y * a + 2 * b * x)
    (by linarith [hx.parameter_pos, hy.parameter_pos]) hx.mean_pos hy.mean_pos
    (by nlinarith only [hfirst]) (by nlinarith only [hsecond]) (by nlinarith only [he])
  have hleft := length_biased_component_eq_conditions p q x y a b c
    hx.parameter_pos hy.parameter_pos hx.mean_pos hx.third_bound hy.second_bound
    (by nlinarith only [hmix.1])
  have hright := length_biased_component_eq_conditions q p y x b a d
    hy.parameter_pos hx.parameter_pos hy.mean_pos hy.third_bound hx.second_bound
    (by nlinarith only [hmix.2])
  refine ⟨hright.1, hleft.1, ?_⟩
  have hscaled : (p + 1) * x * (q * x - p * y) = 0 := by
    nlinarith only [congrArg (fun z : ℝ ↦ q * z) hright.1,
      congrArg (fun z : ℝ ↦ p * z) hleft.2]
  have hcross : q * x = p * y := sub_eq_zero.mp
    ((mul_eq_zero.mp hscaled).resolve_left
      (ne_of_gt (mul_pos (by linarith [hx.parameter_pos]) hx.mean_pos)))
  apply (div_eq_div_iff (ne_of_gt hx.parameter_pos) (ne_of_gt hy.parameter_pos)).2
  nlinarith only [hcross]

end SSPRK
