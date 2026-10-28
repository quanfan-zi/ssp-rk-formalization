import SSPRK.Radius
import SSPRK.RKSubstochastic
import Mathlib.Topology.Sequences

/-!
# Feasibility of the absolute-monotonicity endpoint

The endpoint compactness argument in the proof of V2.10, Theorem 5.1.  Substochasticity keeps the
Runge--Kutta transforms in a compact entrywise box, so singularity cannot first
occur at a positive finite endpoint.
-/

open scoped BigOperators ENNReal

namespace SSPRK

noncomputable section

/-- Complete absolute monotonicity is preserved by a sequential limit. -/
theorem absolutelyMonotoneAt_of_tendsto {s : ℕ} (A : Matrix (Fin s) (Fin s) ℝ)
    (b : Fin s → ℝ) {rseq : ℕ → ℝ} {r : ℝ}
    (hrseq : Filter.Tendsto rseq Filter.atTop (nhds r))
    (ham : ∀ n, 0 < rseq n ∧ AbsolutelyMonotoneAt A b (rseq n)) :
    AbsolutelyMonotoneAt A b r := by
  letI : FirstCountableTopology (Matrix (Fin s) (Fin s) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin s → Fin s → ℝ))
  have hp_sub (n : ℕ) : Substochastic (rkP (rseq n) A) := by
    exact rkP_substochastic (rseq n) A (ham n).2.det_ne_zero (ham n).2.stages
      (ham n).2.matrix_nonneg
  have hp_mem (n : ℕ) :
      rkP (rseq n) A ∈ (Set.Icc (0 : ℝ) 1).matrix := by
    rw [Set.mem_matrix]
    intro i j
    exact ⟨(hp_sub n).nonneg i j, (hp_sub n).entry_le_one i j⟩
  obtain ⟨P, hP, φ, hφ, hP_tendsto⟩ :=
    (isCompact_Icc.matrix.tendsto_subseq hp_mem)
  have hr_subseq : Filter.Tendsto (rseq ∘ φ) Filter.atTop (nhds r) :=
    hrseq.comp hφ.tendsto_atTop
  have hm_tendsto : Filter.Tendsto (fun n ↦ rkM (rseq (φ n)) A) Filter.atTop
      (nhds (1 - P)) := by
    simpa only [Function.comp_apply, one_sub_rkP_eq_rkM] using
      hP_tendsto.const_sub (1 : Matrix (Fin s) (Fin s) ℝ)
  have hn_tendsto : Filter.Tendsto (fun n ↦ rkN (rseq (φ n)) A) Filter.atTop
      (nhds (rkN r A)) := by
    simpa only [rkN, Function.comp_apply] using
      tendsto_const_nhds.add (hr_subseq.smul_const A)
  have hmul_tendsto : Filter.Tendsto
      (fun n ↦ rkN (rseq (φ n)) A * rkM (rseq (φ n)) A) Filter.atTop
      (nhds (rkN r A * (1 - P))) := hn_tendsto.mul hm_tendsto
  have hright : rkN r A * (1 - P) = 1 := by
    apply tendsto_nhds_unique hmul_tendsto
    apply tendsto_const_nhds.congr'
    filter_upwards [] with n
    exact (rkN_mul_rkM (rseq (φ n)) A (ham (φ n)).2.det_ne_zero).symm
  have hinv : (rkN r A).det ≠ 0 := by
    intro hsing
    have hdet := congrArg Matrix.det hright
    simp [Matrix.det_mul, hsing] at hdet
  have hm_eq : rkM r A = 1 - P := by
    calc
      rkM r A = rkM r A * 1 := (Matrix.mul_one _).symm
      _ = rkM r A * (rkN r A * (1 - P)) := by rw [hright]
      _ = (rkM r A * rkN r A) * (1 - P) := (Matrix.mul_assoc _ _ _).symm
      _ = 1 - P := by rw [rkM_mul_rkN r A hinv, Matrix.one_mul]
  have hm_tendsto' : Filter.Tendsto (fun n ↦ rkM (rseq (φ n)) A) Filter.atTop
      (nhds (rkM r A)) := by
    rw [hm_eq]
    exact hm_tendsto
  have hstages_tendsto : Filter.Tendsto
      (fun n ↦ Matrix.mulVec (rkM (rseq (φ n)) A) (ones s)) Filter.atTop
      (nhds (Matrix.mulVec (rkM r A) (ones s))) := by
    exact ((continuous_id.matrix_mulVec continuous_const).tendsto (rkM r A)).comp hm_tendsto'
  have hp_eq : rkP r A = P := by
    rw [rkP, hm_eq]
    abel
  have houtput_tendsto : Filter.Tendsto
      (fun n ↦ Matrix.vecMul b (rkM (rseq (φ n)) A)) Filter.atTop
      (nhds (Matrix.vecMul b (rkM r A))) := by
    exact ((continuous_const.matrix_vecMul continuous_id).tendsto (rkM r A)).comp hm_tendsto'
  have hdot_tendsto : Filter.Tendsto
      (fun n ↦ dotProduct (Matrix.vecMul b (rkM (rseq (φ n)) A)) (ones s)) Filter.atTop
      (nhds (dotProduct (Matrix.vecMul b (rkM r A)) (ones s))) := by
    exact ((continuous_id.dotProduct continuous_const).tendsto
      (Matrix.vecMul b (rkM r A))).comp houtput_tendsto
  have hmass_tendsto : Filter.Tendsto
      (fun n ↦ 1 - rseq (φ n) *
        dotProduct (Matrix.vecMul b (rkM (rseq (φ n)) A)) (ones s)) Filter.atTop
      (nhds (1 - r * dotProduct (Matrix.vecMul b (rkM r A)) (ones s))) := by
    exact tendsto_const_nhds.sub (hr_subseq.mul hdot_tendsto)
  refine
    { det_ne_zero := ?_
      stages := ?_
      matrix_nonneg := ?_
      output_nonneg := ?_
      output_mass := ?_ }
  · simpa only [rkN] using hinv
  · intro i
    apply ge_of_tendsto (tendsto_pi_nhds.mp hstages_tendsto i)
    filter_upwards [] with n
    exact (ham (φ n)).2.stages i
  · intro i j
    have hij : 0 ≤ rkP r A i j := by
      rw [hp_eq]
      exact (Set.mem_matrix.mp hP i j).1
    rw [rkP_eq_r_smul_mul r A hinv] at hij
    simpa only [rkM, rkN] using hij
  · intro i
    apply ge_of_tendsto (tendsto_pi_nhds.mp houtput_tendsto i)
    filter_upwards [] with n
    exact (ham (φ n)).2.output_nonneg i
  · apply ge_of_tendsto hmass_tendsto
    filter_upwards [] with n
    simpa only [rkM, rkN, ones] using (ham (φ n)).2.output_mass

/-- The feasible set, including its distinguished zero element, is closed. -/
theorem isClosed_feasibleRadii {s : ℕ} (A : Matrix (Fin s) (Fin s) ℝ)
    (b : Fin s → ℝ) : IsClosed (feasibleRadii A b) := by
  rw [← isSeqClosed_iff_isClosed]
  intro rseq r hrseq_mem hrseq_tendsto
  have hr_nonneg : 0 ≤ r := by
    apply ge_of_tendsto hrseq_tendsto
    filter_upwards [] with n
    rcases hrseq_mem n with hzero | ⟨hn, _⟩
    · rw [hzero]
    · exact hn.le
  rcases hr_nonneg.eq_or_lt with rfl | hr
  · exact Or.inl rfl
  · right
    refine ⟨hr, ?_⟩
    have heventually : ∀ᶠ n in Filter.atTop,
        0 < rseq n ∧ AbsolutelyMonotoneAt A b (rseq n) := by
      have hpos : ∀ᶠ n in Filter.atTop, 0 < rseq n :=
        hrseq_tendsto (isOpen_Ioi.mem_nhds hr)
      filter_upwards [hpos] with n hn
      exact ⟨hn, ((hrseq_mem n).resolve_left hn.ne').2⟩
    rw [Filter.eventually_atTop] at heventually
    obtain ⟨n₀, hn₀⟩ := heventually
    apply absolutelyMonotoneAt_of_tendsto A b
      (rseq := fun n ↦ rseq (n + n₀))
    · exact hrseq_tendsto.comp (Filter.tendsto_add_atTop_nat n₀)
    · intro n
      exact hn₀ (n + n₀) (by omega)

/-- Endpoint step in V2.10, Theorem 5.1: a finite complete absolute-monotonicity radius belongs to
the feasible set. -/
theorem absoluteMonotonicityRadius_toReal_mem_feasibleRadii {s : ℕ}
    (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ)
    (hfinite : absoluteMonotonicityRadius A b < ⊤) :
    (absoluteMonotonicityRadius A b).toReal ∈ feasibleRadii A b := by
  have hfinite' : absoluteMonotonicityRadius A b ≠ ⊤ := hfinite.ne
  have hnonempty : (feasibleRadii A b).Nonempty := ⟨0, Or.inl rfl⟩
  have hupper {x : ℝ} (hx : x ∈ feasibleRadii A b) :
      x ≤ (absoluteMonotonicityRadius A b).toReal := by
    rw [← ENNReal.ofReal_le_iff_le_toReal hfinite']
    rw [absoluteMonotonicityRadius]
    exact le_iSup_of_le x (le_iSup_of_le hx (le_refl _))
  have hbounded : BddAbove (feasibleRadii A b) :=
    ⟨(absoluteMonotonicityRadius A b).toReal, fun _ hx ↦ hupper hx⟩
  have hsup_mem : sSup (feasibleRadii A b) ∈ feasibleRadii A b :=
    (isClosed_feasibleRadii A b).csSup_mem hnonempty hbounded
  have hsup_le : sSup (feasibleRadii A b) ≤
      (absoluteMonotonicityRadius A b).toReal :=
    csSup_le hnonempty fun _ hx ↦ hupper hx
  have hsup_nonneg : 0 ≤ sSup (feasibleRadii A b) :=
    le_csSup hbounded (Or.inl rfl)
  have hradius_le : absoluteMonotonicityRadius A b ≤
      ENNReal.ofReal (sSup (feasibleRadii A b)) := by
    rw [absoluteMonotonicityRadius]
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    exact ENNReal.ofReal_le_ofReal (le_csSup hbounded hx)
  have hradius_toReal_le : (absoluteMonotonicityRadius A b).toReal ≤
      sSup (feasibleRadii A b) :=
    (ENNReal.le_ofReal_iff_toReal_le hfinite' hsup_nonneg).mp hradius_le
  rw [le_antisymm hradius_toReal_le hsup_le]
  exact hsup_mem

/-- At a positive finite radius, all five endpoint absolute-monotonicity conditions hold. -/
theorem absolutelyMonotoneAt_absoluteMonotonicityRadius {s : ℕ}
    (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ)
    (hpos : 0 < absoluteMonotonicityRadius A b)
    (hfinite : absoluteMonotonicityRadius A b < ⊤) :
    AbsolutelyMonotoneAt A b (absoluteMonotonicityRadius A b).toReal := by
  have hpos_real : 0 < (absoluteMonotonicityRadius A b).toReal :=
    ENNReal.toReal_pos hpos.ne' hfinite.ne
  exact ((absoluteMonotonicityRadius_toReal_mem_feasibleRadii A b hfinite).resolve_left
    hpos_real.ne').2

end

end SSPRK
