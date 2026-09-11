import SSPRK.ErlangUniformizedWeights
import SSPRK.NilpotentLongPath
import SSPRK.OrderedPhaseChain
import SSPRK.PhaseTypeReindex

/-!
# Minimal Erlang phase-type rigidity

The spectral and graph proof of Lemma 4.7: exact-rate uniformization is nilpotent,
a longest positive path orders the states, and maximal occupation forces the chain.
No variance or third-moment equality characterization is used.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SSPRK.PhaseTypeData

noncomputable section

/-- The expected discrete occupation row of a phase-type representation. -/
def occupation {s : ℕ} (d : PhaseTypeData s) : Fin s → ℝ :=
  Matrix.vecMul d.initial d.green

lemma occupation_nonneg {s : ℕ} (d : PhaseTypeData s) (j : Fin s) :
    0 ≤ d.occupation j := by
  unfold occupation Matrix.vecMul dotProduct green
  exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (d.initial_nonneg i)
    (d.substochastic.inv_nonneg d.transient i j)

/-- Discrete occupation satisfies the incoming-flow balance equation. -/
lemma occupation_balance {s : ℕ} (d : PhaseTypeData s) (j : Fin s) :
    d.occupation j = d.initial j + ∑ i, d.occupation i * d.transition i j := by
  have h := congrArg (fun v : Fin s → ℝ ↦ v j)
    (show Matrix.vecMul d.occupation (1 - d.transition) = d.initial by
      rw [occupation, Matrix.vecMul_vecMul, green,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr d.transient), Matrix.vecMul_one])
  dsimp only at h
  rw [Matrix.vecMul_sub, Matrix.vecMul_one] at h
  change d.occupation j - (∑ i, d.occupation i * d.transition i j) = d.initial j at h
  linarith

/-- The Erlang mean fixes total occupation at the Erlang clock rate. -/
lemma sum_occupation_of_measure_eq_gamma {s : ℕ} (d : PhaseTypeData s)
    (κ : ℝ) (hs : 0 < s) (hκ : 0 < κ) (hrate : d.rate = κ)
    (hlaw : d.measure = gammaMeasure (s : ℝ) κ) : ∑ j, d.occupation j = s := by
  have hmean := d.integral_id_measure
  rw [hlaw, integral_id_gammaMeasure (Nat.cast_pos.mpr hs) hκ, hrate] at hmean
  have hdot : dotProduct d.initial (d.green.mulVec (fun _ ↦ 1)) = (s : ℝ) := by
    field_simp [hκ.ne'] at hmean
    exact hmean.symm
  rw [Matrix.dotProduct_mulVec] at hdot
  simpa only [occupation, dotProduct, mul_one] using hdot

/-- A nilpotent exact-rate Erlang representation is a deterministic ordered chain. -/
theorem exists_ordered_chain_of_nilpotent_gamma {s : ℕ} (d : PhaseTypeData s)
    (κ : ℝ) (hs : 0 < s) (hκ : 0 < κ) (hrate : d.rate = κ)
    (hmass : d.mass = 1) (hlaw : d.measure = gammaMeasure (s : ℝ) κ)
    (hnil : d.transition ^ s = 0) :
    ∃ f : Fin s ≃ Fin s,
      (∀ i, d.initial (f i) = if i.val = 0 then 1 else 0) ∧
      ∀ i j, d.transition (f i) (f j) = if j.val = i.val + 1 then 1 else 0 := by
  have hw : 0 < d.weight (s - 1) := by
    rw [d.weight_eq_ite_of_transition_pow_eq_zero_and_gamma κ hs hκ hrate hmass hlaw hnil]
    simp [show s - 1 + 1 = s by omega]
  obtain ⟨i, j, hi, hij, _⟩ := d.exists_positive_initial_power_exit_of_weight_pos hw
  obtain ⟨f, hf0, _, hadj, hforward⟩ :=
    nilpotent_long_path_order_of_pos hs d.transition d.substochastic.nonneg hnil hij
  let a := d.reindex f
  have hapos : ∀ k, 0 < a.occupation k := by
    apply occupation_pos_of_adjacent a.transition a.initial a.occupation
      a.substochastic.nonneg a.initial_nonneg a.occupation_nonneg
    · intro k hk
      have hk0 : k = ⟨0, hs⟩ := Fin.ext hk
      simpa only [a, reindex, Function.comp_apply, hk0, hf0] using hi
    · exact hadj
    · exact a.occupation_balance
  have hamean : ∑ k, a.occupation k = s := by
    apply a.sum_occupation_of_measure_eq_gamma κ hs hκ hrate
    exact (d.measure_reindex f).trans hlaw
  have hamass : ∑ k, a.initial k = 1 := (d.mass_reindex f).trans hmass
  exact ⟨f, ordered_chain_of_maximal_occupation a.transition a.initial a.occupation
    a.substochastic.nonneg a.substochastic.row_sum_le hforward a.initial_nonneg
    hamass hapos hamean a.occupation_balance⟩

/-- Lemma 4.7 in minimal dimension, proved by the spectral and longest-path argument. -/
theorem erlang_rigidity_of_measure_eq_gamma {s : ℕ} (d : PhaseTypeData s)
    (κ : ℝ) (hs : 0 < s) (hκ : 0 < κ) (hmass : d.mass = 1)
    (hlaw : d.measure = gammaMeasure (s : ℝ) κ) :
    ∃ f : Fin s ≃ Fin s,
      d.generator.submatrix f f = (-κ) • chainD s ∧
      ∀ i, d.initial (f i) = if i.val + 1 = s then 1 else 0 := by
  have hchar :=
    (d.eq_num_phases_and_charpoly_of_le_erlang_shape κ hs hκ hmass hlaw le_rfl).2
  let u := d.erlangUniformization κ hκ hchar
  obtain ⟨g, hπ, hP⟩ := u.exists_ordered_chain_of_nilpotent_gamma κ hs hκ rfl
    (d.erlangUniformization_mass κ hκ hchar hmass)
    ((d.erlangUniformization_measure κ hκ hchar).trans hlaw)
    (d.erlangUniformization_transition_pow κ hκ hchar)
  let f : Fin s ≃ Fin s := Fin.revPerm.trans g
  have hT : u.transition.submatrix f f = shiftDown s :=
    successor_reverse_eq_shiftDown (fun i j ↦ u.transition (g i) (g j)) hP
  refine ⟨f, ?_, ?_⟩
  · rw [← d.erlangUniformization_generator κ hκ hchar]
    change u.generator.submatrix f f = (-κ) • chainD s
    ext i j
    have ht := congrArg (fun M : Matrix (Fin s) (Fin s) ℝ ↦ M i j) hT
    change u.transition (f i) (f j) = shiftDown s i j at ht
    simp only [generator, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.sub_apply, Matrix.one_apply, f.injective.eq_iff, ht, chainD]
    change κ * (shiftDown s i j - if i = j then 1 else 0) =
      -κ * ((1 - shiftDown s) i j)
    simp only [Matrix.sub_apply, Matrix.one_apply]
    ring
  · intro i
    have hi := hπ i.rev
    have hrev : i.rev.val = 0 ↔ i.val + 1 = s := by
      simp only [Fin.rev]
      omega
    simpa only [u, erlangUniformization, FiniteSubgenerator.uniformize, hrev,
      f, Equiv.trans_apply, Fin.revPerm_apply] using hi

/-- At most `s` phases representing Erlang shape `s` have exactly `s` states and the chain form. -/
theorem erlang_rigidity_of_num_phases_le {m s : ℕ} (d : PhaseTypeData m)
    (κ : ℝ) (hs : 0 < s) (hκ : 0 < κ) (hmass : d.mass = 1)
    (hlaw : d.measure = gammaMeasure (s : ℝ) κ) (hm : m ≤ s) :
    m = s ∧ ∃ f : Fin s ≃ Fin m,
      d.generator.submatrix f f = (-κ) • chainD s ∧
      ∀ i, d.initial (f i) = if i.val + 1 = s then 1 else 0 := by
  have heq :=
    (d.eq_num_phases_and_charpoly_of_le_erlang_shape κ hs hκ hmass hlaw hm).1
  subst m
  exact ⟨rfl, d.erlang_rigidity_of_measure_eq_gamma κ hs hκ hmass hlaw⟩

end

end SSPRK.PhaseTypeData
