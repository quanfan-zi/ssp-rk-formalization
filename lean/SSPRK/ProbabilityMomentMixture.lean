import SSPRK.MomentCountableMixture
import SSPRK.PhaseTypeMoments

/-!
# Countable mixtures of probability laws with three moments

A residual atom at zero completes a countable subprobability mixture.  A summable
weighted third moment controls the weighted first and second moments on nonnegative
support, so the countable moment-class theorem applies without extra summability data.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace SSPRK

/-- Complete a countable mixture to a probability law by placing its missing mass at zero. -/
noncomputable def probabilityMomentMixture (π : ℕ → ℝ) (μ : ℕ → Measure ℝ) :
    Measure ℝ :=
  ENNReal.ofReal (1 - ∑' i, π i) • Measure.dirac 0 +
    Measure.sum (fun i ↦ ENNReal.ofReal (π i) • μ i)

/-- The residual zero atom makes the countable subprobability mixture a probability law. -/
theorem isProbabilityMeasure_probabilityMomentMixture (π : ℕ → ℝ)
    (μ : ℕ → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hπ : ∀ i, 0 ≤ π i) (hπsum : Summable π) (hmass : ∑' i, π i ≤ 1) :
    IsProbabilityMeasure (probabilityMomentMixture π μ) := by
  apply PhaseTypeData.isProbabilityMeasure_atom_add_sum
  · exact hμ
  · rw [← ENNReal.ofReal_tsum_of_nonneg hπ hπsum]
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr hmass) (tsum_nonneg hπ)]
    simp

private lemma nonneg_le_one_add_cube {t : ℝ} (ht : 0 ≤ t) : t ≤ 1 + t ^ 3 := by
  by_cases htle : t ≤ 1
  · exact htle.trans (le_add_of_nonneg_right (pow_nonneg ht 3))
  · have hone : 1 ≤ t := le_of_not_ge htle
    have ht_sq : t ≤ t ^ 2 := by
      nlinarith only [mul_nonneg ht (sub_nonneg.mpr hone)]
    have hsq_cube : t ^ 2 ≤ t ^ 3 := by
      nlinarith only [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hone)]
    linarith

private lemma sq_le_one_add_cube {t : ℝ} (ht : 0 ≤ t) : t ^ 2 ≤ 1 + t ^ 3 := by
  by_cases htle : t ≤ 1
  · have hsquare : t ^ 2 ≤ 1 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr htle) (by linarith : 0 ≤ 1 + t)]
    nlinarith only [hsquare, pow_nonneg ht 3]
  · have hone : 1 ≤ t := le_of_not_ge htle
    have hsq_cube : t ^ 2 ≤ t ^ 3 := by
      nlinarith only [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hone)]
    linarith

private lemma integral_id_le_one_add_cube (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hnonneg : ∀ᵐ t ∂μ, 0 ≤ t) (hint1 : Integrable (fun t : ℝ ↦ t) μ)
    (hint3 : Integrable (fun t : ℝ ↦ t ^ 3) μ) :
    ∫ t, t ∂μ ≤ 1 + ∫ t, t ^ 3 ∂μ := by
  have hint_sum : Integrable (fun t : ℝ ↦ 1 + t ^ 3) μ :=
    (integrable_const (1 : ℝ)).add hint3
  calc
    ∫ t, t ∂μ ≤ ∫ t, 1 + t ^ 3 ∂μ :=
      integral_mono_ae hint1 hint_sum (hnonneg.mono fun t ht ↦ nonneg_le_one_add_cube ht)
    _ = 1 + ∫ t, t ^ 3 ∂μ := by
      rw [integral_add (integrable_const (1 : ℝ)) hint3]
      simp

private lemma integral_sq_le_one_add_cube (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hnonneg : ∀ᵐ t ∂μ, 0 ≤ t) (hint2 : Integrable (fun t : ℝ ↦ t ^ 2) μ)
    (hint3 : Integrable (fun t : ℝ ↦ t ^ 3) μ) :
    ∫ t, t ^ 2 ∂μ ≤ 1 + ∫ t, t ^ 3 ∂μ := by
  have hint_sum : Integrable (fun t : ℝ ↦ 1 + t ^ 3) μ :=
    (integrable_const (1 : ℝ)).add hint3
  calc
    ∫ t, t ^ 2 ∂μ ≤ ∫ t, 1 + t ^ 3 ∂μ :=
      integral_mono_ae hint2 hint_sum (hnonneg.mono fun t ht ↦ sq_le_one_add_cube ht)
    _ = 1 + ∫ t, t ^ 3 ∂μ := by
      rw [integral_add (integrable_const (1 : ℝ)) hint3]
      simp

private lemma summable_weighted_first_second {k : ℝ} (π : ℕ → ℝ)
    (μ : ℕ → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hnonneg : ∀ i, ∀ᵐ t ∂μ i, 0 ≤ t)
    (hint1 : ∀ i, Integrable (fun t : ℝ ↦ t) (μ i))
    (hint2 : ∀ i, Integrable (fun t : ℝ ↦ t ^ 2) (μ i))
    (hint3 : ∀ i, Integrable (fun t : ℝ ↦ t ^ 3) (μ i))
    (hπ : ∀ i, 0 ≤ π i) (hπsum : Summable π)
    (hclass : ∀ i, MomentClass k (∫ t, t ∂μ i)
      (∫ t, t ^ 2 ∂μ i) (∫ t, t ^ 3 ∂μ i))
    (hweighted3 : Summable fun i ↦ π i * ∫ t, t ^ 3 ∂μ i) :
    Summable (fun i ↦ π i * ∫ t, t ∂μ i) ∧
      Summable (fun i ↦ π i * ∫ t, t ^ 2 ∂μ i) := by
  have hmajor : Summable (fun i ↦ π i + π i * ∫ t, t ^ 3 ∂μ i) :=
    hπsum.add hweighted3
  constructor
  · apply Summable.of_nonneg_of_le
      (fun i ↦ mul_nonneg (hπ i) (hclass i).mean_pos.le) _ hmajor
    intro i
    haveI : IsProbabilityMeasure (μ i) := hμ i
    calc
      π i * ∫ t, t ∂μ i ≤ π i * (1 + ∫ t, t ^ 3 ∂μ i) :=
        mul_le_mul_of_nonneg_left
          (integral_id_le_one_add_cube (μ i) (hnonneg i) (hint1 i) (hint3 i)) (hπ i)
      _ = π i + π i * ∫ t, t ^ 3 ∂μ i := by ring
  · apply Summable.of_nonneg_of_le
      (fun i ↦ mul_nonneg (hπ i) (hclass i).second_nonneg) _ hmajor
    intro i
    haveI : IsProbabilityMeasure (μ i) := hμ i
    calc
      π i * ∫ t, t ^ 2 ∂μ i ≤ π i * (1 + ∫ t, t ^ 3 ∂μ i) :=
        mul_le_mul_of_nonneg_left
          (integral_sq_le_one_add_cube (μ i) (hnonneg i) (hint2 i) (hint3 i)) (hπ i)
      _ = π i + π i * ∫ t, t ^ 3 ∂μ i := by ring

private lemma probabilityMomentMixture_pow_moment (π : ℕ → ℝ)
    (μ : ℕ → Measure ℝ) (n : ℕ) (hn : 0 < n)
    (hπ : ∀ i, 0 ≤ π i) (hnonneg : ∀ i, ∀ᵐ t ∂μ i, 0 ≤ t)
    (hint : ∀ i, Integrable (fun t : ℝ ↦ t ^ n) (μ i))
    (hsum : Summable fun i ↦ π i * ∫ t, t ^ n ∂μ i) :
    Integrable (fun t : ℝ ↦ t ^ n) (probabilityMomentMixture π μ) ∧
      ∫ t, t ^ n ∂probabilityMomentMixture π μ =
        ∑' i, π i * ∫ t, t ^ n ∂μ i := by
  have hpositive := weighted_measure_moment μ π
    (fun i ↦ ∫ t, t ^ n ∂μ i) (fun t ↦ t ^ n)
    (∑' i, π i * ∫ t, t ^ n ∂μ i) hπ hint
    (fun i ↦ (hnonneg i).mono fun t ht ↦ pow_nonneg ht n) (fun _ ↦ rfl) hsum.hasSum
  unfold probabilityMomentMixture
  exact atom_add_measure_moment _ _ (fun t : ℝ ↦ t ^ n) hpositive.1
    (zero_pow hn.ne') |>.imp id fun heq ↦ heq.trans hpositive.2

/-- The first three moments of the completed mixture are its weighted component moments. -/
theorem probabilityMomentMixture_first_three_moments {k : ℝ} (π : ℕ → ℝ)
    (μ : ℕ → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hnonneg : ∀ i, ∀ᵐ t ∂μ i, 0 ≤ t)
    (hint1 : ∀ i, Integrable (fun t : ℝ ↦ t) (μ i))
    (hint2 : ∀ i, Integrable (fun t : ℝ ↦ t ^ 2) (μ i))
    (hint3 : ∀ i, Integrable (fun t : ℝ ↦ t ^ 3) (μ i))
    (hπ : ∀ i, 0 ≤ π i) (hπsum : Summable π)
    (hclass : ∀ i, MomentClass k (∫ t, t ∂μ i)
      (∫ t, t ^ 2 ∂μ i) (∫ t, t ^ 3 ∂μ i))
    (hweighted3 : Summable fun i ↦ π i * ∫ t, t ^ 3 ∂μ i) :
    (Integrable (fun t : ℝ ↦ t) (probabilityMomentMixture π μ) ∧
      ∫ t, t ∂probabilityMomentMixture π μ = ∑' i, π i * ∫ t, t ∂μ i) ∧
    (Integrable (fun t : ℝ ↦ t ^ 2) (probabilityMomentMixture π μ) ∧
      ∫ t, t ^ 2 ∂probabilityMomentMixture π μ =
        ∑' i, π i * ∫ t, t ^ 2 ∂μ i) ∧
    (Integrable (fun t : ℝ ↦ t ^ 3) (probabilityMomentMixture π μ) ∧
      ∫ t, t ^ 3 ∂probabilityMomentMixture π μ =
        ∑' i, π i * ∫ t, t ^ 3 ∂μ i) := by
  obtain ⟨hsum1, hsum2⟩ := summable_weighted_first_second π μ hμ hnonneg
    hint1 hint2 hint3 hπ hπsum hclass hweighted3
  refine ⟨?_, ?_, ?_⟩
  · simpa only [pow_one] using
      probabilityMomentMixture_pow_moment π μ 1 (by norm_num) hπ hnonneg
        (fun i ↦ by simpa only [pow_one] using hint1 i) (by simpa only [pow_one] using hsum1)
  · exact probabilityMomentMixture_pow_moment π μ 2 (by norm_num) hπ hnonneg hint2 hsum2
  · exact probabilityMomentMixture_pow_moment π μ 3 (by norm_num) hπ hnonneg hint3 hweighted3

/-- The first three moments of the completed countable mixture form the same moment class. -/
theorem probabilityMomentMixture_moment_class {k : ℝ} (π : ℕ → ℝ)
    (μ : ℕ → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hnonneg : ∀ i, ∀ᵐ t ∂μ i, 0 ≤ t)
    (hint1 : ∀ i, Integrable (fun t : ℝ ↦ t) (μ i))
    (hint2 : ∀ i, Integrable (fun t : ℝ ↦ t ^ 2) (μ i))
    (hint3 : ∀ i, Integrable (fun t : ℝ ↦ t ^ 3) (μ i))
    (hπ : ∀ i, 0 ≤ π i) (hπsum : Summable π) (hmass : ∑' i, π i ≤ 1)
    (hclass : ∀ i, MomentClass k (∫ t, t ∂μ i)
      (∫ t, t ^ 2 ∂μ i) (∫ t, t ^ 3 ∂μ i))
    (hweighted3 : Summable fun i ↦ π i * ∫ t, t ^ 3 ∂μ i)
    (hmean : 0 < ∫ t, t ∂probabilityMomentMixture π μ) :
    MomentClass k (∫ t, t ∂probabilityMomentMixture π μ)
      (∫ t, t ^ 2 ∂probabilityMomentMixture π μ)
      (∫ t, t ^ 3 ∂probabilityMomentMixture π μ) := by
  obtain ⟨hm1, hm2, hm3⟩ := probabilityMomentMixture_first_three_moments
    π μ hμ hnonneg hint1 hint2 hint3 hπ hπsum hclass hweighted3
  obtain ⟨hsum1, hsum2⟩ := summable_weighted_first_second π μ hμ hnonneg
    hint1 hint2 hint3 hπ hπsum hclass hweighted3
  rw [hm1.2, hm2.2, hm3.2]
  apply MomentClass.countable_mixture π _ _ _ hπ hπsum hmass hclass
    hsum1 hsum2 hweighted3
  rwa [← hm1.2]

/-- Equality in the completed mixture's third-moment bound is characterized componentwise. -/
theorem probabilityMomentMixture_third_eq_iff {k : ℝ} (π : ℕ → ℝ)
    (μ : ℕ → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hnonneg : ∀ i, ∀ᵐ t ∂μ i, 0 ≤ t)
    (hint1 : ∀ i, Integrable (fun t : ℝ ↦ t) (μ i))
    (hint2 : ∀ i, Integrable (fun t : ℝ ↦ t ^ 2) (μ i))
    (hint3 : ∀ i, Integrable (fun t : ℝ ↦ t ^ 3) (μ i))
    (hπ : ∀ i, 0 ≤ π i) (hπsum : Summable π)
    (hclass : ∀ i, MomentClass k (∫ t, t ∂μ i)
      (∫ t, t ^ 2 ∂μ i) (∫ t, t ^ 3 ∂μ i))
    (hweighted3 : Summable fun i ↦ π i * ∫ t, t ^ 3 ∂μ i)
    (hmean : 0 < ∫ t, t ∂probabilityMomentMixture π μ) :
    (k + 2) * (∫ t, t ^ 2 ∂probabilityMomentMixture π μ) ^ 2 =
        (k + 1) * (∫ t, t ∂probabilityMomentMixture π μ) *
          (∫ t, t ^ 3 ∂probabilityMomentMixture π μ) ↔
      ∃ q : ℝ, ∀ i, 0 < π i →
        (k + 2) * (∫ t, t ^ 2 ∂μ i) ^ 2 =
            (k + 1) * (∫ t, t ∂μ i) * (∫ t, t ^ 3 ∂μ i) ∧
          (∫ t, t ^ 2 ∂μ i) / (∫ t, t ∂μ i) = q := by
  obtain ⟨hm1, hm2, hm3⟩ := probabilityMomentMixture_first_three_moments
    π μ hμ hnonneg hint1 hint2 hint3 hπ hπsum hclass hweighted3
  obtain ⟨hsum1, hsum2⟩ := summable_weighted_first_second π μ hμ hnonneg
    hint1 hint2 hint3 hπ hπsum hclass hweighted3
  rw [hm1.2, hm2.2, hm3.2]
  apply MomentClass.countable_mixture_third_eq_iff π _ _ _ hπ hclass
    hsum1 hsum2 hweighted3
  rwa [← hm1.2]

end SSPRK
