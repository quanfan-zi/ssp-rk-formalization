import SSPRK.MomentAlgebra
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

/-!
# Probability laws of independent sums and their first three moments

The additive convolution is the pushforward of the product probability measure under
coordinate addition. Its integral moment formulas connect independent sums to `MomentClass.add`.
-/

open MeasureTheory

namespace SSPRK

noncomputable def independentSumLaw (μ ν : Measure ℝ) : Measure ℝ := μ ∗ ν

theorem independentSumLaw_eq_map (μ ν : Measure ℝ) :
    independentSumLaw μ ν = (μ.prod ν).map (fun z : ℝ × ℝ ↦ z.1 + z.2) := rfl

variable (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

instance independentSumLaw_probability : IsProbabilityMeasure (independentSumLaw μ ν) := by
  unfold independentSumLaw
  infer_instance

theorem independentSumLaw_coordinates_independent :
    ProbabilityTheory.IndepFun (fun z : ℝ × ℝ ↦ z.1) (fun z : ℝ × ℝ ↦ z.2) (μ.prod ν) :=
  ProbabilityTheory.indepFun_prod measurable_id measurable_id

omit [IsProbabilityMeasure μ] in
theorem independentSumLaw_ae_nonneg (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (hν : ∀ᵐ y ∂ν, 0 ≤ y) :
    ∀ᵐ z ∂independentSumLaw μ ν, 0 ≤ z := by
  rw [independentSumLaw_eq_map, ae_map_iff (by fun_prop) (by measurability)]
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [hμ] with x hx
  filter_upwards [hν] with y hy
  exact add_nonneg hx hy

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem independentSumLaw_integrable_iff (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable f (independentSumLaw μ ν) ↔
      Integrable (fun z : ℝ × ℝ ↦ f (z.1 + z.2)) (μ.prod ν) := by
  rw [independentSumLaw_eq_map]
  exact integrable_map_measure hf.aestronglyMeasurable (by fun_prop)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem independentSumLaw_integral (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x, f x ∂independentSumLaw μ ν) = ∫ z, f (z.1 + z.2) ∂μ.prod ν := by
  rw [independentSumLaw_eq_map]
  exact integral_map (by fun_prop) hf.aestronglyMeasurable

theorem independentSumLaw_first_moment
    (hμ : Integrable (fun x : ℝ ↦ x) μ) (hν : Integrable (fun x : ℝ ↦ x) ν) :
    Integrable (fun x : ℝ ↦ x) (independentSumLaw μ ν) ∧
      (∫ x, x ∂independentSumLaw μ ν) = (∫ x, x ∂μ) + ∫ y, y ∂ν := by
  refine ⟨(independentSumLaw_integrable_iff μ ν _ continuous_id).2
    ((hμ.comp_fst ν).add (hν.comp_snd μ)), ?_⟩
  rw [independentSumLaw_integral μ ν (fun x : ℝ ↦ x) (by fun_prop),
    integral_add (hμ.comp_fst ν) (hν.comp_snd μ),
    integral_fun_fst (fun x : ℝ ↦ x), integral_fun_snd (fun x : ℝ ↦ x)]
  simp

theorem independentSumLaw_second_moment
    (hμ1 : Integrable (fun x : ℝ ↦ x) μ) (hν1 : Integrable (fun x : ℝ ↦ x) ν)
    (hμ2 : Integrable (fun x : ℝ ↦ x ^ 2) μ) (hν2 : Integrable (fun x : ℝ ↦ x ^ 2) ν) :
    Integrable (fun x : ℝ ↦ x ^ 2) (independentSumLaw μ ν) ∧
      (∫ x, x ^ 2 ∂independentSumLaw μ ν) =
        (∫ x, x ^ 2 ∂μ) + (∫ y, y ^ 2 ∂ν) + 2 * (∫ x, x ∂μ) * ∫ y, y ∂ν := by
  have he : (fun z : ℝ × ℝ ↦ (z.1 + z.2) ^ 2) =
      (fun z ↦ z.1 ^ 2 + z.2 ^ 2 + 2 * (z.1 * z.2)) := funext fun z ↦ by ring
  have hprod := ((hμ2.comp_fst ν).add (hν2.comp_snd μ)).add
    ((hμ1.mul_prod hν1).const_mul 2)
  have hsum : Integrable (fun z : ℝ × ℝ ↦ z.1 ^ 2 + z.2 ^ 2) (μ.prod ν) :=
    (hμ2.comp_fst ν).add (hν2.comp_snd μ)
  refine ⟨(independentSumLaw_integrable_iff μ ν _ (by fun_prop)).2 (he ▸ hprod), ?_⟩
  rw [independentSumLaw_integral μ ν _ (by fun_prop), he]
  rw [integral_add hsum
    ((hμ1.mul_prod hν1).const_mul 2),
    integral_add (hμ2.comp_fst ν) (hν2.comp_snd μ), integral_const_mul,
    integral_fun_fst (fun x : ℝ ↦ x ^ 2), integral_fun_snd (fun x : ℝ ↦ x ^ 2),
    integral_prod_mul (fun x : ℝ ↦ x) (fun x : ℝ ↦ x)]
  simp [mul_assoc]

theorem independentSumLaw_third_moment
    (hμ1 : Integrable (fun x : ℝ ↦ x) μ) (hν1 : Integrable (fun x : ℝ ↦ x) ν)
    (hμ2 : Integrable (fun x : ℝ ↦ x ^ 2) μ) (hν2 : Integrable (fun x : ℝ ↦ x ^ 2) ν)
    (hμ3 : Integrable (fun x : ℝ ↦ x ^ 3) μ) (hν3 : Integrable (fun x : ℝ ↦ x ^ 3) ν) :
    Integrable (fun x : ℝ ↦ x ^ 3) (independentSumLaw μ ν) ∧
      (∫ x, x ^ 3 ∂independentSumLaw μ ν) =
        (∫ x, x ^ 3 ∂μ) + (∫ y, y ^ 3 ∂ν) +
          3 * (∫ x, x ^ 2 ∂μ) * (∫ y, y ∂ν) +
          3 * (∫ x, x ∂μ) * (∫ y, y ^ 2 ∂ν) := by
  have he : (fun z : ℝ × ℝ ↦ (z.1 + z.2) ^ 3) =
      (fun z ↦ z.1 ^ 3 + z.2 ^ 3 + 3 * (z.1 ^ 2 * z.2) +
        3 * (z.1 * z.2 ^ 2)) := funext fun z ↦ by ring
  have hsum : Integrable (fun z : ℝ × ℝ ↦ z.1 ^ 3 + z.2 ^ 3) (μ.prod ν) :=
    (hμ3.comp_fst ν).add (hν3.comp_snd μ)
  have hc1 : Integrable (fun z : ℝ × ℝ ↦ 3 * (z.1 ^ 2 * z.2)) (μ.prod ν) :=
    (hμ2.mul_prod hν1).const_mul 3
  have hc2 : Integrable (fun z : ℝ × ℝ ↦ 3 * (z.1 * z.2 ^ 2)) (μ.prod ν) :=
    (hμ1.mul_prod hν2).const_mul 3
  have hsum2 : Integrable (fun z : ℝ × ℝ ↦
      z.1 ^ 3 + z.2 ^ 3 + 3 * (z.1 ^ 2 * z.2)) (μ.prod ν) := hsum.add hc1
  refine ⟨(independentSumLaw_integrable_iff μ ν _ (by fun_prop)).2
    (he ▸ hsum2.add hc2), ?_⟩
  rw [independentSumLaw_integral μ ν _ (by fun_prop), he,
    integral_add hsum2 hc2, integral_add hsum hc1,
    integral_add (hμ3.comp_fst ν) (hν3.comp_snd μ)]
  simp only [integral_const_mul]
  rw [integral_fun_fst (fun x : ℝ ↦ x ^ 3), integral_fun_snd (fun x : ℝ ↦ x ^ 3),
    integral_prod_mul (fun x : ℝ ↦ x ^ 2) (fun x : ℝ ↦ x),
    integral_prod_mul (fun x : ℝ ↦ x) (fun x : ℝ ↦ x ^ 2)]
  simp [mul_assoc]

theorem independentSumLaw_momentClass {p q : ℝ}
    (hμ1 : Integrable (fun x : ℝ ↦ x) μ) (hν1 : Integrable (fun x : ℝ ↦ x) ν)
    (hμ2 : Integrable (fun x : ℝ ↦ x ^ 2) μ) (hν2 : Integrable (fun x : ℝ ↦ x ^ 2) ν)
    (hμ3 : Integrable (fun x : ℝ ↦ x ^ 3) μ) (hν3 : Integrable (fun x : ℝ ↦ x ^ 3) ν)
    (hμ : MomentClass p (∫ x, x ∂μ) (∫ x, x ^ 2 ∂μ) (∫ x, x ^ 3 ∂μ))
    (hν : MomentClass q (∫ x, x ∂ν) (∫ x, x ^ 2 ∂ν) (∫ x, x ^ 3 ∂ν)) :
    MomentClass (p + q) (∫ x, x ∂independentSumLaw μ ν)
      (∫ x, x ^ 2 ∂independentSumLaw μ ν) (∫ x, x ^ 3 ∂independentSumLaw μ ν) := by
  rw [(independentSumLaw_first_moment μ ν hμ1 hν1).2,
    (independentSumLaw_second_moment μ ν hμ1 hν1 hμ2 hν2).2,
    (independentSumLaw_third_moment μ ν hμ1 hν1 hμ2 hν2 hμ3 hν3).2]
  exact hμ.add hν

end SSPRK
