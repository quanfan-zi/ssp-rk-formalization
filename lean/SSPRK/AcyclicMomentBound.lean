import SSPRK.AcyclicHomogeneous
import SSPRK.CompleteHomogeneous
import SSPRK.PhaseTypeLawEquality
import SSPRK.ErlangAdjacentMoments

/-!
# Adjacent moment bounds for acyclic phase-type laws

We follow the finite decreasing-path proof: apply Schur's inequality to each
path's holding-time polynomial and then apply weighted Cauchy--Schwarz to the
path mixture. Equality forces full-length paths with a common constant holding
mean, so the first two moments attain the variance bound and identify the Erlang law.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SSPRK

/-- The factorial moment of the sum of holding times along a finite path. -/
noncomputable def pathMoment (as : List ℝ) (k : ℕ) : ℝ :=
  (k.factorial : ℝ) * pathPolynomial as k

theorem pathMoment_pos (as : List ℝ) (hne : as ≠ [])
    (hpos : ∀ a ∈ as, 0 < a) (k : ℕ) : 0 < pathMoment as k :=
  mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos k)) (pathPolynomial_pos as hne hpos k)

/-- The path bound uses the actual number of states visited. -/
theorem pathMoment_schur (as : List ℝ) (hne : as ≠ [])
    (hpos : ∀ a ∈ as, 0 < a) (k : ℕ) :
    ((as.length : ℝ) + k + 1) * pathMoment as (k + 1) ^ 2 ≤
      ((as.length : ℝ) + k) * pathMoment as k * pathMoment as (k + 2) := by
  simpa only [pathMoment, pathPolynomial_eq_completeHomogeneous] using
    completeHomogeneous_factorial_schur (List.length_pos_iff.mpr hne)
      (fun i : Fin as.length ↦ as[i.val])
      (fun i ↦ (hpos _ (List.getElem_mem i.isLt)).le) k

/-- The adjacent moment product is strictly larger than the middle square. -/
lemma pathMoment_adjacent_defect_pos (as : List ℝ) (hne : as ≠ [])
    (hpos : ∀ a ∈ as, 0 < a) (k : ℕ) :
    0 < pathMoment as k * pathMoment as (k + 2) - pathMoment as (k + 1) ^ 2 := by
  have h := pathMoment_schur as hne hpos k
  have hsq := sq_pos_of_pos (pathMoment_pos as hne hpos (k + 1))
  by_contra! hdiff
  have hn := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ (as.length : ℝ) + k by positivity) hdiff
  nlinarith only [h, hsq, hn]

/-- Padding a shorter path to the ambient state count weakens its bound. -/
theorem pathMoment_schur_of_length_le (as : List ℝ) (hne : as ≠ [])
    (hpos : ∀ a ∈ as, 0 < a) (s : ℕ) (hlen : as.length ≤ s) (k : ℕ) :
    ((s : ℝ) + k + 1) * pathMoment as (k + 1) ^ 2 ≤
      ((s : ℝ) + k) * pathMoment as k * pathMoment as (k + 2) := by
  have h := pathMoment_schur as hne hpos k
  have hdiff := pathMoment_adjacent_defect_pos as hne hpos k
  have hlen' : 0 ≤ (s : ℝ) - as.length := sub_nonneg.mpr (Nat.cast_le.mpr hlen)
  nlinarith only [h, mul_nonneg hlen' hdiff.le]

/-- A sharp ambient bound requires a full-length path with equal holding means. -/
theorem pathMoment_eq_of_schur_eq (as : List ℝ) (hne : as ≠ [])
    (hpos : ∀ a ∈ as, 0 < a) (s : ℕ) (hlen : as.length ≤ s) (k : ℕ)
    (heq : ((s : ℝ) + k + 1) * pathMoment as (k + 1) ^ 2 =
      ((s : ℝ) + k) * pathMoment as k * pathMoment as (k + 2)) :
    as.length = s ∧ ∃ c : ℝ, ∀ a ∈ as, a = c := by
  have h := pathMoment_schur as hne hpos k
  have hdiff := pathMoment_adjacent_defect_pos as hne hpos k
  have hlen' : (s : ℝ) ≤ as.length := by
    by_contra! hlt
    nlinarith only [h, heq, mul_pos (sub_pos.mpr hlt) hdiff]
  have hlength : as.length = s := Nat.le_antisymm hlen (Nat.cast_le.mp hlen')
  refine ⟨hlength, ?_⟩
  have heq' : ((as.length : ℝ) + k + 1) *
      ((Nat.factorial (k + 1) : ℝ) *
        completeHomogeneous (fun i : Fin as.length ↦ as[i.val]) (k + 1)) ^ 2 =
      ((as.length : ℝ) + k) * ((Nat.factorial k : ℝ) *
        completeHomogeneous (fun i : Fin as.length ↦ as[i.val]) k) *
        ((Nat.factorial (k + 2) : ℝ) *
          completeHomogeneous (fun i : Fin as.length ↦ as[i.val]) (k + 2)) := by
    simpa only [pathMoment, pathPolynomial_eq_completeHomogeneous, hlength] using heq
  obtain ⟨c, hc⟩ := (completeHomogeneous_factorial_schur_eq_iff
    (List.length_pos_iff.mpr hne) (fun i : Fin as.length ↦ as[i.val])
    (fun i ↦ (hpos _ (List.getElem_mem i.isLt)).le) k).mp heq'
  refine ⟨c, ?_⟩
  intro a ha
  obtain ⟨i, hi, hia⟩ := List.getElem_of_mem ha
  simpa only [hia] using hc ⟨i, hi⟩

/-- A finite list sum is a sum over its positions, preserving repeated paths. -/
lemma pathSum_eq_sum_get (f : List ℝ → ℝ) (paths : List AcyclicPath) :
    pathSum f paths = ∑ i : Fin paths.length, paths[i.val].1 * f paths[i.val].2 := by
  rw [pathSum, ← List.ofFn_getElem_eq_map, List.sum_ofFn]

namespace PhaseTypeData

/-- The actual integral is the finite mixture of full factorial path moments. -/
theorem integral_pow_eq_pathMoment_sum {s : ℕ} (d : PhaseTypeData s)
    (hd : d.IsLowerAcyclic) (hmass : d.mass = 1) (k : ℕ) :
    ∫ x, x ^ k ∂d.measure = ∑ i : Fin d.acyclicPaths.length,
      d.acyclicPaths[i.val].1 * pathMoment d.acyclicPaths[i.val].2 k := by
  rw [d.integral_pow_eq_acyclicPaths_of_mass_one hd hmass k, pathSum_eq_sum_get,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by simp only [pathMoment]; ring

theorem acyclic_weight_sum {s : ℕ} (d : PhaseTypeData s)
    (hd : d.IsLowerAcyclic) (hmass : d.mass = 1) :
    (∑ i : Fin d.acyclicPaths.length, d.acyclicPaths[i.val].1) = 1 := by
  simpa only [pathSum_eq_sum_get, mul_one, hmass] using d.acyclicPaths_mass hd

/-- Every natural moment of a mass-one acyclic PH law is positive. -/
theorem acyclic_integral_pow_pos {s : ℕ} (d : PhaseTypeData s)
    (hd : d.IsLowerAcyclic) (hmass : d.mass = 1) (k : ℕ) :
    0 < ∫ x, x ^ k ∂d.measure := by
  have hv (i : Fin d.acyclicPaths.length) :=
    d.acyclicPaths_valid d.acyclicPaths[i.val] (List.getElem_mem i.isLt)
  have hw := d.acyclic_weight_sum hd hmass
  have hwpos : 0 < ∑ i : Fin d.acyclicPaths.length, d.acyclicPaths[i.val].1 := by
    rw [hw]
    norm_num
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ ↦ (hv i).1)).mp hwpos
  rw [d.integral_pow_eq_pathMoment_sum hd hmass]
  exact Finset.sum_pos'
    (fun j _ ↦ mul_nonneg (hv j).1
      (pathMoment_pos _ (hv j).2.2.1 (hv j).2.1 k).le)
    ⟨i, Finset.mem_univ i, mul_pos hi (pathMoment_pos _ (hv i).2.2.1 (hv i).2.1 k)⟩

/-- Weighted Cauchy--Schwarz transfers the path bound to the PH law. -/
theorem acyclic_moment_bound {s : ℕ} (d : PhaseTypeData s) (hs : 0 < s)
    (hd : d.IsLowerAcyclic) (hmass : d.mass = 1) (k : ℕ) :
    ((s : ℝ) + k + 1) * (∫ x, x ^ (k + 1) ∂d.measure) ^ 2 ≤
      ((s : ℝ) + k) * (∫ x, x ^ k ∂d.measure) * (∫ x, x ^ (k + 2) ∂d.measure) := by
  have hv (i : Fin d.acyclicPaths.length) :=
    d.acyclicPaths_valid d.acyclicPaths[i.val] (List.getElem_mem i.isLt)
  simp only [d.integral_pow_eq_pathMoment_sum hd hmass]
  exact weighted_quadratic_bound (ι := Fin d.acyclicPaths.length)
    (fun i ↦ d.acyclicPaths[i.val].1)
    (fun i ↦ pathMoment d.acyclicPaths[i.val].2 k)
    (fun i ↦ pathMoment d.acyclicPaths[i.val].2 (k + 1))
    (fun i ↦ pathMoment d.acyclicPaths[i.val].2 (k + 2)) (by positivity) (by positivity)
    (fun i ↦ (hv i).1)
    (fun i ↦ (pathMoment_pos _ (hv i).2.2.1 (hv i).2.1 k).le)
    (fun i ↦ (pathMoment_pos _ (hv i).2.2.1 (hv i).2.1 (k + 2)).le)
    (fun i ↦ pathMoment_schur_of_length_le _ (hv i).2.2.1 (hv i).2.1 s (hv i).2.2.2 k)

/-- At equality every positive-weight path is full length and has equal holding means. -/
theorem acyclic_sharp_path {s : ℕ} (d : PhaseTypeData s) (hs : 0 < s)
    (hd : d.IsLowerAcyclic) (hmass : d.mass = 1) (k : ℕ)
    (heq : ((s : ℝ) + k + 1) * (∫ x, x ^ (k + 1) ∂d.measure) ^ 2 =
      ((s : ℝ) + k) * (∫ x, x ^ k ∂d.measure) * (∫ x, x ^ (k + 2) ∂d.measure)) :
    ∀ i : Fin d.acyclicPaths.length, 0 < d.acyclicPaths[i.val].1 →
      d.acyclicPaths[i.val].2.length = s ∧
        ∃ c : ℝ, ∀ a ∈ d.acyclicPaths[i.val].2, a = c := by
  have hv (i : Fin d.acyclicPaths.length) :=
    d.acyclicPaths_valid d.acyclicPaths[i.val] (List.getElem_mem i.isLt)
  have hm : 0 < ∑ i : Fin d.acyclicPaths.length,
      d.acyclicPaths[i.val].1 * pathMoment d.acyclicPaths[i.val].2 k := by
    rw [← d.integral_pow_eq_pathMoment_sum hd hmass]
    exact d.acyclic_integral_pow_pos hd hmass k
  simp only [d.integral_pow_eq_pathMoment_sum hd hmass] at heq
  obtain ⟨q, hq⟩ := (weighted_quadratic_eq_iff (ι := Fin d.acyclicPaths.length)
    (c := (s : ℝ) + k + 1) (d := (s : ℝ) + k) (fun i ↦ d.acyclicPaths[i.val].1)
    (fun i ↦ pathMoment d.acyclicPaths[i.val].2 k)
    (fun i ↦ pathMoment d.acyclicPaths[i.val].2 (k + 1))
    (fun i ↦ pathMoment d.acyclicPaths[i.val].2 (k + 2)) (by positivity)
    (fun i ↦ (hv i).1) (fun i ↦ pathMoment_pos _ (hv i).2.2.1 (hv i).2.1 k)
    (fun i ↦ pathMoment_schur_of_length_le _ (hv i).2.2.1 (hv i).2.1 s (hv i).2.2.2 k)
    hm).mp heq
  exact fun i hi ↦ pathMoment_eq_of_schur_eq _ (hv i).2.2.1 (hv i).2.1 s
    (hv i).2.2.2 k (hq i hi).1

/-- Full-length sharp paths share the holding mean of the greatest transient state. -/
theorem acyclic_sharp_holdingMean {s : ℕ} (d : PhaseTypeData s) (hs : 0 < s)
    (hd : d.IsLowerAcyclic) (hmass : d.mass = 1) (k : ℕ)
    (heq : ((s : ℝ) + k + 1) * (∫ x, x ^ (k + 1) ∂d.measure) ^ 2 =
      ((s : ℝ) + k) * (∫ x, x ^ k ∂d.measure) * (∫ x, x ^ (k + 2) ∂d.measure))
    (top : Fin s) (htop : top.val + 1 = s) :
    ∀ i : Fin d.acyclicPaths.length, 0 < d.acyclicPaths[i.val].1 →
      d.acyclicPaths[i.val].2.length = s ∧
        ∀ a ∈ d.acyclicPaths[i.val].2, a = d.holdingMean top := by
  intro i hi
  obtain ⟨hlen, c, hc⟩ := d.acyclic_sharp_path hs hd hmass k heq i hi
  have hhead := d.acyclicPaths_full_length_head top htop d.acyclicPaths[i.val]
    (List.getElem_mem i.isLt) hlen
  obtain ⟨tail, htail⟩ := List.head?_eq_some_iff.mp hhead
  have hm : d.holdingMean top ∈ d.acyclicPaths[i.val].2 := by rw [htail]; simp
  exact ⟨hlen, fun a ha ↦ (hc a ha).trans (hc _ hm).symm⟩

private lemma sum_weighted_eq_of_eq_on_pos {ι : Type*} [Fintype ι]
    (w f : ι → ℝ) (c : ℝ) (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (hc : ∀ i, 0 < w i → f i = c) : ∑ i, w i * f i = c := by
  calc
    _ = ∑ i, w i * c := by
      apply Finset.sum_congr rfl
      intro i _
      rcases (hw i).eq_or_lt with hz | hp
      · simp [← hz]
      · rw [hc i hp]
    _ = (∑ i, w i) * c := (Finset.sum_mul _ _ _).symm
    _ = c := by rw [hmass, one_mul]

/-- Sharpness at any order fixes the first two moments to those of the full Erlang chain. -/
theorem acyclic_first_two_of_sharp {s : ℕ} (d : PhaseTypeData s) (hs : 0 < s)
    (hd : d.IsLowerAcyclic) (hmass : d.mass = 1) (k : ℕ)
    (heq : ((s : ℝ) + k + 1) * (∫ x, x ^ (k + 1) ∂d.measure) ^ 2 =
      ((s : ℝ) + k) * (∫ x, x ^ k ∂d.measure) * (∫ x, x ^ (k + 2) ∂d.measure))
    (top : Fin s) (htop : top.val + 1 = s) :
    (∫ x, x ∂d.measure) = (s : ℝ) * d.holdingMean top ∧
      (∫ x, x ^ 2 ∂d.measure) =
        (s : ℝ) * ((s : ℝ) + 1) * d.holdingMean top ^ 2 := by
  have hv (i : Fin d.acyclicPaths.length) :=
    d.acyclicPaths_valid d.acyclicPaths[i.val] (List.getElem_mem i.isLt)
  have hc := d.acyclic_sharp_holdingMean hs hd hmass k heq top htop
  constructor
  · rw [show (∫ x, x ∂d.measure) = (∫ x, x ^ (1 : ℕ) ∂d.measure) by simp,
      d.integral_pow_eq_pathMoment_sum hd hmass]
    apply sum_weighted_eq_of_eq_on_pos _ _ _ (fun i ↦ (hv i).1)
      (d.acyclic_weight_sum hd hmass)
    intro i hi
    simp only [pathMoment, pathPolynomial_one_const _ _ (hc i hi).2,
      (hc i hi).1, Nat.factorial_one, Nat.cast_one, one_mul]
  · rw [d.integral_pow_eq_pathMoment_sum hd hmass]
    apply sum_weighted_eq_of_eq_on_pos _ _ _ (fun i ↦ (hv i).1)
      (d.acyclic_weight_sum hd hmass)
    intro i hi
    rw [pathMoment, pathPolynomial_two_const _ _ (hc i hi).2, (hc i hi).1]
    norm_num
    ring

/-- The full Erlang law follows from the sharp first-two-moment classification. -/
theorem acyclic_erlang_of_sharp {s : ℕ} (d : PhaseTypeData s) (hs : 0 < s)
    (hd : d.IsLowerAcyclic) (hmass : d.mass = 1) (k : ℕ)
    (heq : ((s : ℝ) + k + 1) * (∫ x, x ^ (k + 1) ∂d.measure) ^ 2 =
      ((s : ℝ) + k) * (∫ x, x ^ k ∂d.measure) * (∫ x, x ^ (k + 2) ∂d.measure)) :
    ∃ κ : ℝ, 0 < κ ∧ d.measure = gammaMeasure (s : ℝ) κ := by
  let top : Fin s := ⟨s - 1, by omega⟩
  have htop : top.val + 1 = s := by dsimp [top]; omega
  obtain ⟨hfirst, hsecond⟩ := d.acyclic_first_two_of_sharp hs hd hmass k heq top htop
  have hmean : 0 < ∫ x, x ∂d.measure := by
    rw [hfirst]
    exact mul_pos (Nat.cast_pos.mpr hs) (d.holdingMean_pos top)
  apply (d.variance_eq_iff_erlang hs hmean).mp
  rw [d.variance_measure, hfirst, hsecond]
  field_simp
  ring

/-- Every adjacent ratio is bounded sharply for a topologically ordered PH representation. -/
theorem acyclic_moment_ratio {s : ℕ} (d : PhaseTypeData s) (hs : 0 < s)
    (hd : d.IsLowerAcyclic) (hmass : d.mass = 1) (k : ℕ) :
    ((s : ℝ) + k + 1) / ((s : ℝ) + k) ≤
      (∫ x, x ^ k ∂d.measure) * (∫ x, x ^ (k + 2) ∂d.measure) /
        (∫ x, x ^ (k + 1) ∂d.measure) ^ 2 ∧
    ((∫ x, x ^ k ∂d.measure) * (∫ x, x ^ (k + 2) ∂d.measure) /
        (∫ x, x ^ (k + 1) ∂d.measure) ^ 2 = ((s : ℝ) + k + 1) / ((s : ℝ) + k) ↔
      ∃ κ : ℝ, 0 < κ ∧ d.measure = gammaMeasure (s : ℝ) κ) := by
  have hden : 0 < (s : ℝ) + k := by positivity
  have hmiddle := sq_pos_of_pos (d.acyclic_integral_pow_pos hd hmass (k + 1))
  constructor
  · apply (div_le_div_iff₀ hden hmiddle).mpr
    nlinarith only [d.acyclic_moment_bound hs hd hmass k]
  · constructor
    · intro heq
      apply d.acyclic_erlang_of_sharp hs hd hmass k
      have hc := (div_eq_div_iff hmiddle.ne' hden.ne').mp heq
      nlinarith only [hc]
    · rintro ⟨κ, hκ, hmeasure⟩
      rw [hmeasure]
      exact gamma_adjacent_moment_ratio (Nat.cast_pos.mpr hs) hκ k

end PhaseTypeData
end SSPRK
