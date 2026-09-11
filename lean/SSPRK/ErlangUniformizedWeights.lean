import SSPRK.PhaseTypeErlangNilpotent
import SSPRK.PhaseTypeLaw
import SSPRK.PhaseTypeMoments

/-!
# Uniformized absorption weights for an Erlang phase-type law

An `s`-phase representation of an Erlang law can be uniformized at the Erlang
rate. Its transition matrix is the nonnegative nilpotent shift of the original
generator. The resulting absorption-count distribution is concentrated at
exactly `s` clock events.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Polynomial

namespace SSPRK
namespace PhaseTypeData

noncomputable section

/-- The generator of phase-type data is a finite subgenerator. -/
theorem generator_finiteSubgenerator {s : ℕ} (d : PhaseTypeData s) :
    FiniteSubgenerator d.generator := by
  constructor
  · intro i j hij
    simp [generator, hij, mul_nonneg d.rate_pos.le (d.substochastic.nonneg i j)]
  · intro i
    unfold generator
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.one_apply]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    have hone : (∑ j : Fin s, if i = j then (1 : ℝ) else 0) = 1 := by simp
    rw [hone]
    exact mul_nonpos_of_nonneg_of_nonpos d.rate_pos.le
      (sub_nonpos.mpr (d.substochastic.row_sum_le i))
  · rw [d.neg_generator, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ d.rate_pos.ne') d.transient

/-- Uniformize an Erlang generator at its Erlang rate. -/
def erlangUniformization {s : ℕ} (d : PhaseTypeData s) (κ : ℝ) (hκ : 0 < κ)
    (hchar : d.generator.charpoly = (Polynomial.X + Polynomial.C κ) ^ s) :
    PhaseTypeData s :=
  d.generator_finiteSubgenerator.uniformize d.initial d.initial_nonneg d.initial_mass_le κ hκ
    (fun i ↦ by rw [d.generator_diag_eq_neg_of_charpoly_eq κ hchar i]; simp)

/-- The new clock rate is the Erlang rate. -/
@[simp]
theorem erlangUniformization_rate {s : ℕ} (d : PhaseTypeData s) (κ : ℝ) (hκ : 0 < κ)
    (hchar : d.generator.charpoly = (Polynomial.X + Polynomial.C κ) ^ s) :
    (d.erlangUniformization κ hκ hchar).rate = κ := rfl

/-- The uniformized transition is the scaled nonnegative generator shift. -/
theorem erlangUniformization_transition {s : ℕ} (d : PhaseTypeData s) (κ : ℝ)
    (hκ : 0 < κ)
    (hchar : d.generator.charpoly = (Polynomial.X + Polynomial.C κ) ^ s) :
    (d.erlangUniformization κ hκ hchar).transition = κ⁻¹ • d.erlangShift κ := by
  unfold erlangUniformization FiniteSubgenerator.uniformize FiniteSubgenerator.transition
    erlangShift
  rw [smul_add, smul_smul, inv_mul_cancel₀ hκ.ne', one_smul]
  abel_nf

/-- The uniformized transition is nilpotent with exponent `s`. -/
theorem erlangUniformization_transition_pow {s : ℕ} (d : PhaseTypeData s) (κ : ℝ)
    (hκ : 0 < κ)
    (hchar : d.generator.charpoly = (Polynomial.X + Polynomial.C κ) ^ s) :
    (d.erlangUniformization κ hκ hchar).transition ^ s = 0 := by
  rw [d.erlangUniformization_transition κ hκ hchar, smul_pow,
    d.erlangShift_pow_eq_zero κ hchar, smul_zero]

/-- Uniformizing at the Erlang rate preserves the generator. -/
theorem erlangUniformization_generator {s : ℕ} (d : PhaseTypeData s) (κ : ℝ)
    (hκ : 0 < κ)
    (hchar : d.generator.charpoly = (Polynomial.X + Polynomial.C κ) ^ s) :
    (d.erlangUniformization κ hκ hchar).generator = d.generator := by
  unfold erlangUniformization
  apply FiniteSubgenerator.generator_uniformize

/-- Uniformizing at the Erlang rate preserves the phase-type law. -/
theorem erlangUniformization_measure {s : ℕ} (d : PhaseTypeData s) (κ : ℝ)
    (hκ : 0 < κ)
    (hchar : d.generator.charpoly = (Polynomial.X + Polynomial.C κ) ^ s) :
    (d.erlangUniformization κ hκ hchar).measure = d.measure := by
  apply PhaseTypeData.measure_eq_of_initial_generator_eq
  · rfl
  · exact d.erlangUniformization_generator κ hκ hchar

/-- Uniformization preserves the initial mass. -/
theorem erlangUniformization_mass {s : ℕ} (d : PhaseTypeData s) (κ : ℝ)
    (hκ : 0 < κ)
    (hchar : d.generator.charpoly = (Polynomial.X + Polynomial.C κ) ^ s)
    (hmass : d.mass = 1) :
    (d.erlangUniformization κ hκ hchar).mass = 1 := by
  simpa [erlangUniformization, mass] using hmass

/-- A nilpotent `s`-state representation of the corresponding Erlang law absorbs
after exactly `s` clock events. -/
theorem weight_eq_ite_of_transition_pow_eq_zero_and_gamma {s : ℕ}
    (e : PhaseTypeData s) (κ : ℝ) (hs : 0 < s) (hκ : 0 < κ)
    (hrate : e.rate = κ) (hmass : e.mass = 1)
    (hlaw : e.measure = gammaMeasure (s : ℝ) κ)
    (hpow : e.transition ^ s = 0) (n : ℕ) :
    e.weight n = if n + 1 = s then 1 else 0 := by
  have hweight : HasSum e.weight 1 := by
    simpa [hmass] using e.hasSum_weight
  have hmean := e.integral_id_measure
  rw [hlaw, integral_id_gammaMeasure (Nat.cast_pos.mpr hs) hκ, hrate] at hmean
  have hdot : dotProduct e.initial (e.green.mulVec (fun _ ↦ 1)) = (s : ℝ) := by
    field_simp [hκ.ne'] at hmean
    exact hmean.symm
  have hcount : HasSum (fun m : ℕ ↦ (m + 1 : ℝ) * e.weight m) (s : ℝ) := by
    simpa [hdot] using e.hasSum_first_count_moment
  have hweight_zero_of_ge : ∀ {m : ℕ}, s ≤ m → e.weight m = 0 := by
    intro m hm
    unfold weight
    rw [pow_eq_zero_of_le hm hpow]
    simp
  let deficit : ℕ → ℝ := fun m ↦ ((s : ℝ) - (m + 1 : ℝ)) * e.weight m
  have hdeficit : HasSum deficit 0 := by
    have h := (hweight.mul_left (s : ℝ)).sub hcount
    convert h using 1
    · ext m
      simp only [deficit]
      ring
    · ring
  have hdeficit_nonneg : ∀ m, 0 ≤ deficit m := by
    intro m
    by_cases hm : s ≤ m
    · simp [deficit, hweight_zero_of_ge hm]
    · have hm' : m + 1 ≤ s := by omega
      have hmcast : (m : ℝ) + 1 ≤ (s : ℝ) := by exact_mod_cast hm'
      exact mul_nonneg (sub_nonneg.mpr hmcast) (e.weight_nonneg m)
  have hdeficit_zero : ∀ m, deficit m = 0 := by
    intro m
    apply le_antisymm
    · rw [← hdeficit.tsum_eq]
      exact hdeficit.summable.le_tsum m (fun k _ ↦ hdeficit_nonneg k)
    · exact hdeficit_nonneg m
  have hweight_zero_of_lt : ∀ {m : ℕ}, m + 1 < s → e.weight m = 0 := by
    intro m hm
    have hmcast : (m : ℝ) + 1 < (s : ℝ) := by exact_mod_cast hm
    have hcoeff : 0 < (s : ℝ) - (m + 1 : ℝ) := sub_pos.mpr hmcast
    exact (mul_eq_zero.mp (hdeficit_zero m)).resolve_left hcoeff.ne'
  split_ifs with hn
  · have hother : ∀ m, m ≠ n → e.weight m = 0 := by
      intro m hmn
      by_cases hm : m + 1 < s
      · exact hweight_zero_of_lt hm
      · exact hweight_zero_of_ge (by omega)
    have hsum := hweight.tsum_eq
    rw [tsum_eq_single n (fun m hmn ↦ hother m hmn)] at hsum
    exact hsum
  · by_cases hm : n + 1 < s
    · exact hweight_zero_of_lt hm
    · exact hweight_zero_of_ge (by omega)

/-- The Erlang-rate uniformization has the deterministic absorption-count law. -/
theorem erlangUniformization_weight {s : ℕ} (d : PhaseTypeData s) (κ : ℝ)
    (hs : 0 < s) (hκ : 0 < κ)
    (hchar : d.generator.charpoly = (Polynomial.X + Polynomial.C κ) ^ s)
    (hmass : d.mass = 1) (hlaw : d.measure = gammaMeasure (s : ℝ) κ) (n : ℕ) :
    (d.erlangUniformization κ hκ hchar).weight n =
      if n + 1 = s then 1 else 0 := by
  apply weight_eq_ite_of_transition_pow_eq_zero_and_gamma _ κ hs hκ
  · rfl
  · exact d.erlangUniformization_mass κ hκ hchar hmass
  · exact (d.erlangUniformization_measure κ hκ hchar).trans hlaw
  · exact d.erlangUniformization_transition_pow κ hκ hchar

/-- A positive absorption weight contains a positive initial-to-exit matrix-power entry. -/
theorem exists_positive_initial_power_exit_of_weight_pos {s n : ℕ}
    (e : PhaseTypeData s) (hweight : 0 < e.weight n) :
    ∃ i j, 0 < e.initial i ∧ 0 < (e.transition ^ n) i j ∧ 0 < e.exit j := by
  unfold weight Matrix.mulVec dotProduct at hweight
  have houter_nonneg : ∀ i ∈ Finset.univ,
      0 ≤ e.initial i * ∑ j, (e.transition ^ n) i j * e.exit j := by
    intro i _
    exact mul_nonneg (e.initial_nonneg i) (Finset.sum_nonneg fun j _ ↦
      mul_nonneg ((e.substochastic.pow n).nonneg i j) (e.exit_nonneg j))
  obtain ⟨i, _, hi⟩ :=
    (Finset.sum_pos_iff_of_nonneg houter_nonneg).mp hweight
  have hinner_nonneg : 0 ≤ ∑ j, (e.transition ^ n) i j * e.exit j :=
    Finset.sum_nonneg fun j _ ↦
      mul_nonneg ((e.substochastic.pow n).nonneg i j) (e.exit_nonneg j)
  have hinitial : 0 < e.initial i := by
    rcases (mul_pos_iff.mp hi) with h | h
    · exact h.1
    · exact False.elim ((not_lt_of_ge (e.initial_nonneg i)) h.1)
  have hinner : 0 < ∑ j, (e.transition ^ n) i j * e.exit j := by
    rcases (mul_pos_iff.mp hi) with h | h
    · exact h.2
    · exact False.elim ((not_lt_of_ge hinner_nonneg) h.2)
  have hterm_nonneg : ∀ j ∈ Finset.univ,
      0 ≤ (e.transition ^ n) i j * e.exit j := by
    intro j _
    exact mul_nonneg ((e.substochastic.pow n).nonneg i j) (e.exit_nonneg j)
  obtain ⟨j, _, hj⟩ :=
    (Finset.sum_pos_iff_of_nonneg hterm_nonneg).mp hinner
  have htransition : 0 < (e.transition ^ n) i j := by
    rcases (mul_pos_iff.mp hj) with h | h
    · exact h.1
    · exact False.elim ((not_lt_of_ge ((e.substochastic.pow n).nonneg i j)) h.1)
  have hexit : 0 < e.exit j := by
    rcases (mul_pos_iff.mp hj) with h | h
    · exact h.2
    · exact False.elim ((not_lt_of_ge (e.exit_nonneg j)) h.2)
  exact ⟨i, j, hinitial, htransition, hexit⟩

/-- The deterministic `s`-event weight yields a positive path entry of length `s - 1`. -/
theorem erlangUniformization_exists_positive_long_entry {s : ℕ}
    (d : PhaseTypeData s) (κ : ℝ) (hs : 0 < s) (hκ : 0 < κ)
    (hchar : d.generator.charpoly = (Polynomial.X + Polynomial.C κ) ^ s)
    (hmass : d.mass = 1) (hlaw : d.measure = gammaMeasure (s : ℝ) κ) :
    ∃ i j,
      0 < (d.erlangUniformization κ hκ hchar).initial i ∧
      0 < ((d.erlangUniformization κ hκ hchar).transition ^ (s - 1)) i j ∧
      0 < (d.erlangUniformization κ hκ hchar).exit j := by
  apply exists_positive_initial_power_exit_of_weight_pos
  rw [d.erlangUniformization_weight κ hs hκ hchar hmass hlaw]
  simp [show s - 1 + 1 = s by omega]

/-- Package the Erlang-rate uniformization directly from equality of laws. -/
theorem exists_erlangUniformization_of_measure_eq_gamma {s : ℕ}
    (d : PhaseTypeData s) (κ : ℝ) (hs : 0 < s) (hκ : 0 < κ)
    (hmass : d.mass = 1) (hlaw : d.measure = gammaMeasure (s : ℝ) κ) :
    ∃ e : PhaseTypeData s,
      e.rate = κ ∧
      e.transition = κ⁻¹ • d.erlangShift κ ∧
      e.transition ^ s = 0 ∧
      e.generator = d.generator ∧
      e.measure = d.measure ∧
      e.mass = 1 ∧
      ∀ n, e.weight n = if n + 1 = s then 1 else 0 := by
  have hchar :=
    (d.eq_num_phases_and_charpoly_of_le_erlang_shape κ hs hκ hmass hlaw le_rfl).2
  let e := d.erlangUniformization κ hκ hchar
  refine ⟨e, rfl, d.erlangUniformization_transition κ hκ hchar,
    d.erlangUniformization_transition_pow κ hκ hchar,
    d.erlangUniformization_generator κ hκ hchar,
    d.erlangUniformization_measure κ hκ hchar,
    d.erlangUniformization_mass κ hκ hchar hmass, ?_⟩
  exact fun n ↦ d.erlangUniformization_weight κ hs hκ hchar hmass hlaw n

end

end PhaseTypeData
end SSPRK
