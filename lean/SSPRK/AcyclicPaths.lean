import SSPRK.PhaseTypeEmbeddedChain
import SSPRK.PhaseTypeGeneratorMoments

/-!
# Finite decreasing paths of an acyclic phase-type representation

The path expansion in the proof of V2.10, Theorem 4.4. A path is stored as its
probability weight and the list of mean holding times. Zero-weight paths are retained:
this avoids dividing by their probabilities and does not change any mixture moment.
-/

open MeasureTheory
open scoped BigOperators

namespace SSPRK

/-- A finite path with its probability weight and its successive mean holding times. -/
abbrev AcyclicPath := ℝ × List ℝ

/-- Complete homogeneous polynomials of the holding means, in a recursive list form. -/
noncomputable def pathPolynomial : List ℝ → ℕ → ℝ
  | _, 0 => 1
  | [], _ + 1 => 0
  | a :: as, k + 1 => a * pathPolynomial (a :: as) k + pathPolynomial as (k + 1)
termination_by as k => k + as.length

/-- The weighted sum of an observable of the holding-mean lists. -/
noncomputable def pathSum (f : List ℝ → ℝ) (paths : List AcyclicPath) : ℝ :=
  (paths.map fun p ↦ p.1 * f p.2).sum

@[simp] theorem pathPolynomial_zero (as : List ℝ) : pathPolynomial as 0 = 1 := by
  rw [pathPolynomial]

@[simp] theorem pathPolynomial_nil_succ (k : ℕ) : pathPolynomial [] (k + 1) = 0 := by
  rw [pathPolynomial]

theorem pathPolynomial_cons_succ (a : ℝ) (as : List ℝ) (k : ℕ) :
    pathPolynomial (a :: as) (k + 1) =
      a * pathPolynomial (a :: as) k + pathPolynomial as (k + 1) := by
  rw [pathPolynomial]

theorem pathSum_cons_succ (a : ℝ) (paths : List AcyclicPath) (k : ℕ) :
    pathSum (fun as ↦ pathPolynomial (a :: as) (k + 1)) paths =
      a * pathSum (fun as ↦ pathPolynomial (a :: as) k) paths +
        pathSum (fun as ↦ pathPolynomial as (k + 1)) paths := by
  simp [pathSum, pathPolynomial_cons_succ, mul_add, List.sum_map_add,
    ← List.sum_map_mul_left, mul_left_comm]

namespace PhaseTypeData

/-- A topologically ordered representation: all transient jumps decrease the state index. -/
def IsLowerAcyclic {s : ℕ} (d : PhaseTypeData s) : Prop :=
  ∀ i j, i < j → d.generator i j = 0

/-- A transient state below the current starting state. -/
def lowerState {s : ℕ} (i : Fin s) (j : Fin i.val) : Fin s :=
  ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩

/-- The actual mean holding time at a transient state. -/
noncomputable def holdingMean {s : ℕ} (d : PhaseTypeData s) (i : Fin s) : ℝ :=
  (-d.generator i i)⁻¹

theorem holdingMean_pos {s : ℕ} (d : PhaseTypeData s) (i : Fin s) :
    0 < d.holdingMean i := by
  exact inv_pos.mpr (neg_pos.mpr (d.generator_diag_neg i))

/-- Prefix a transient state to a collection of lower-state paths. -/
noncomputable def prependPaths (weight mean : ℝ) (paths : List AcyclicPath) :
    List AcyclicPath :=
  paths.map fun p ↦ (weight * p.1, mean :: p.2)

/-- All decreasing paths from one transient state, with their embedded-chain weights. -/
noncomputable def acyclicPathsFrom {s : ℕ} (d : PhaseTypeData s) (i : Fin s) :
    List AcyclicPath :=
  (d.embeddedChain.exit i, [d.holdingMean i]) ::
    (List.finRange i.val).flatMap (fun j ↦
      prependPaths (d.embeddedTransition i (lowerState i j)) (d.holdingMean i)
        (d.acyclicPathsFrom (lowerState i j)))
termination_by i.val
decreasing_by exact j.isLt

/-- Mixing the decreasing paths over the initial distribution. -/
noncomputable def acyclicPaths {s : ℕ} (d : PhaseTypeData s) : List AcyclicPath :=
  (List.finRange s).flatMap fun i ↦
    (d.acyclicPathsFrom i).map fun p ↦ (d.initial i * p.1, p.2)

theorem pathSum_prependPaths (f : List ℝ → ℝ) (weight mean : ℝ)
    (paths : List AcyclicPath) :
    pathSum f (prependPaths weight mean paths) =
      weight * pathSum (fun as ↦ f (mean :: as)) paths := by
  simp [pathSum, prependPaths, List.map_map, Function.comp_def, mul_assoc,
    List.sum_map_mul_left]

theorem pathSum_acyclicPathsFrom {s : ℕ} (d : PhaseTypeData s) (i : Fin s)
    (f : List ℝ → ℝ) :
    pathSum f (d.acyclicPathsFrom i) =
      d.embeddedChain.exit i * f [d.holdingMean i] +
        ∑ j : Fin i.val, d.embeddedTransition i (lowerState i j) *
          pathSum (fun as ↦ f (d.holdingMean i :: as))
            (d.acyclicPathsFrom (lowerState i j)) := by
  rw [acyclicPathsFrom]
  simp [pathSum, List.flatMap_def, List.sum_flatten, Function.comp_def,
    prependPaths, List.map_map, mul_assoc, List.sum_map_mul_left,
    ← List.ofFn_eq_map, List.sum_ofFn]

theorem sum_lowerState {s : ℕ} (i : Fin s) (f : Fin s → ℝ)
    (hf : ∀ j, i ≤ j → f j = 0) :
    ∑ j : Fin i.val, f (lowerState i j) = ∑ j : Fin s, f j := by
  refine Fintype.sum_of_injective (lowerState i)
    (fun a b h ↦ Fin.ext (congrArg (fun x : Fin s ↦ x.val) h)) _ _ ?_ (fun _ ↦ rfl)
  intro j hj
  apply hf j
  by_contra hij
  exact hj ⟨⟨j.val, lt_of_not_ge hij⟩, rfl⟩

theorem embeddedTransition_eq_zero_of_le {s : ℕ} (d : PhaseTypeData s)
    (hd : d.IsLowerAcyclic) {i j : Fin s} (hij : i ≤ j) :
    d.embeddedTransition i j = 0 := by
  rcases hij.eq_or_lt with rfl | hij
  · exact d.embeddedTransition_diag i
  · simp [embeddedTransition, ne_of_lt hij, hd i j hij]

theorem embedded_exit_add_lower_sum {s : ℕ} (d : PhaseTypeData s)
    (hd : d.IsLowerAcyclic) (i : Fin s) :
    d.embeddedChain.exit i +
      ∑ j : Fin i.val, d.embeddedTransition i (lowerState i j) = 1 := by
  rw [sum_lowerState i _ (fun j hj ↦ d.embeddedTransition_eq_zero_of_le hd hj)]
  simp [exit, Matrix.mulVec, dotProduct, Matrix.one_apply]

theorem acyclicPathsFrom_mass {s : ℕ} (d : PhaseTypeData s)
    (hd : d.IsLowerAcyclic) (i : Fin s) :
    pathSum (fun _ ↦ 1) (d.acyclicPathsFrom i) = 1 := by
  induction hi : i.val using Nat.strong_induction_on generalizing i with
  | h n ih =>
    rw [pathSum_acyclicPathsFrom]
    have hmass (j : Fin i.val) :
        pathSum (fun _ ↦ 1) (d.acyclicPathsFrom (lowerState i j)) = 1 :=
      ih j.val (hi ▸ j.isLt) (lowerState i j) rfl
    simpa only [hmass, mul_one] using d.embedded_exit_add_lower_sum hd i

theorem pathSum_acyclicPaths {s : ℕ} (d : PhaseTypeData s) (f : List ℝ → ℝ) :
    pathSum f d.acyclicPaths =
      ∑ i, d.initial i * pathSum f (d.acyclicPathsFrom i) := by
  simp [acyclicPaths, pathSum, List.flatMap_def, List.sum_flatten, List.map_map,
    Function.comp_def, mul_assoc, List.sum_map_mul_left, ← List.ofFn_eq_map, List.sum_ofFn]

theorem acyclicPaths_mass {s : ℕ} (d : PhaseTypeData s) (hd : d.IsLowerAcyclic) :
    pathSum (fun _ ↦ 1) d.acyclicPaths = d.mass := by
  simp [pathSum_acyclicPaths, d.acyclicPathsFrom_mass hd, mass]

theorem one_sub_embeddedTransition_mul_continuousGreen {s : ℕ} (d : PhaseTypeData s) :
    (1 - d.embeddedTransition) * d.continuousGreen = d.embeddedHoldingInv := by
  have hdet : (-d.generator).det ≠ 0 := by
    rw [d.neg_generator, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ d.rate_pos.ne') d.transient
  rw [d.one_sub_embeddedTransition, Matrix.mul_assoc, continuousGreen,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.mul_one]

/-- First-step recurrence for the factorial-normalized absorption moments. -/
theorem continuousGreen_moment_succ {s : ℕ} (d : PhaseTypeData s) (i : Fin s) (k : ℕ) :
    (d.continuousGreen ^ (k + 1)).mulVec (fun _ ↦ 1) i =
      d.holdingMean i * (d.continuousGreen ^ k).mulVec (fun _ ↦ 1) i +
        ∑ j, d.embeddedTransition i j *
          (d.continuousGreen ^ (k + 1)).mulVec (fun _ ↦ 1) j := by
  have h := congrArg
    (fun m : Matrix (Fin s) (Fin s) ℝ ↦
      (m * d.continuousGreen ^ k).mulVec (fun _ ↦ 1) i)
    d.one_sub_embeddedTransition_mul_continuousGreen
  simp only [Matrix.mul_assoc, ← pow_succ', Matrix.sub_mul, Matrix.one_mul,
    Matrix.sub_mulVec, Pi.sub_apply, ← Matrix.mulVec_mulVec,
    embeddedHoldingInv, Matrix.mulVec_diagonal] at h
  change _ - ∑ j, d.embeddedTransition i j *
    (d.continuousGreen ^ (k + 1)).mulVec (fun _ ↦ 1) j =
      d.holdingMean i * (d.continuousGreen ^ k).mulVec (fun _ ↦ 1) i at h
  linarith only [h]

theorem pathSum_acyclicPathsFrom_succ {s : ℕ} (d : PhaseTypeData s) (i : Fin s) (k : ℕ) :
    pathSum (fun as ↦ pathPolynomial as (k + 1)) (d.acyclicPathsFrom i) =
      d.holdingMean i * pathSum (fun as ↦ pathPolynomial as k) (d.acyclicPathsFrom i) +
        ∑ j : Fin i.val, d.embeddedTransition i (lowerState i j) *
          pathSum (fun as ↦ pathPolynomial as (k + 1))
            (d.acyclicPathsFrom (lowerState i j)) := by
  rw [d.pathSum_acyclicPathsFrom i (fun as ↦ pathPolynomial as (k + 1)),
    d.pathSum_acyclicPathsFrom i (fun as ↦ pathPolynomial as k)]
  simp_rw [pathSum_cons_succ]
  simp only [pathPolynomial_cons_succ, pathPolynomial_nil_succ, add_zero,
    mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  ring_nf

/-- The finite path mixture gives every factorial-normalized Green moment. -/
theorem pathSum_acyclicPathsFrom_moment {s : ℕ} (d : PhaseTypeData s)
    (hd : d.IsLowerAcyclic) (i : Fin s) (k : ℕ) :
    pathSum (fun as ↦ pathPolynomial as k) (d.acyclicPathsFrom i) =
      (d.continuousGreen ^ k).mulVec (fun _ ↦ 1) i := by
  induction k generalizing i with
  | zero => simpa using d.acyclicPathsFrom_mass hd i
  | succ k ih =>
    induction hi : i.val using Nat.strong_induction_on generalizing i with
    | h n ihrow =>
      rw [d.pathSum_acyclicPathsFrom_succ, d.continuousGreen_moment_succ, ih]
      congr 1
      have hrec (j : Fin i.val) :
          pathSum (fun as ↦ pathPolynomial as (k + 1))
              (d.acyclicPathsFrom (lowerState i j)) =
            (d.continuousGreen ^ (k + 1)).mulVec (fun _ ↦ 1) (lowerState i j) :=
        ihrow j.val (hi ▸ j.isLt) (lowerState i j) rfl
      simp_rw [hrec]
      exact sum_lowerState i
        (fun j ↦ d.embeddedTransition i j *
          (d.continuousGreen ^ (k + 1)).mulVec (fun _ ↦ 1) j) fun j hj ↦ by
        exact mul_eq_zero_of_left (d.embeddedTransition_eq_zero_of_le hd hj) _

/-- Actual PH moments are the finite decreasing-path mixture moments. -/
theorem integral_pow_eq_acyclicPaths {s : ℕ} (d : PhaseTypeData s)
    (hd : d.IsLowerAcyclic) (k : ℕ) (hk : 0 < k) :
    ∫ x, x ^ k ∂d.measure =
      (k.factorial : ℝ) * pathSum (fun as ↦ pathPolynomial as k) d.acyclicPaths := by
  rw [d.integral_pow_eq_continuousGreen k hk, d.pathSum_acyclicPaths]
  simp_rw [d.pathSum_acyclicPathsFrom_moment hd]
  rfl

theorem integral_pow_eq_acyclicPaths_of_mass_one {s : ℕ} (d : PhaseTypeData s)
    (hd : d.IsLowerAcyclic) (hmass : d.mass = 1) (k : ℕ) :
    ∫ x, x ^ k ∂d.measure =
      (k.factorial : ℝ) * pathSum (fun as ↦ pathPolynomial as k) d.acyclicPaths := by
  cases k with
  | zero => simp [d.acyclicPaths_mass hd, hmass]
  | succ k => exact d.integral_pow_eq_acyclicPaths hd (k + 1) (Nat.succ_pos k)

/-- Each enumerated path has nonnegative weight and positive holding means, and cannot
visit more states than its starting index allows. -/
theorem acyclicPathsFrom_valid {s : ℕ} (d : PhaseTypeData s) (i : Fin s)
    (p : AcyclicPath) (hp : p ∈ d.acyclicPathsFrom i) :
    0 ≤ p.1 ∧ (∀ a ∈ p.2, 0 < a) ∧ p.2 ≠ [] ∧ p.2.length ≤ i.val + 1 := by
  induction hi : i.val using Nat.strong_induction_on generalizing i p with
  | h n ih =>
    rw [acyclicPathsFrom, List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp only [List.mem_singleton, forall_eq, List.cons_ne_self, ne_eq,
        not_false_eq_true, List.length_singleton, true_and]
      exact ⟨d.embeddedChain.exit_nonneg i, d.holdingMean_pos i, by omega⟩
    · obtain ⟨j, _, hp⟩ := List.mem_flatMap.mp hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      obtain ⟨hw, hpos, _, hlen⟩ :=
        ih j.val (hi ▸ j.isLt) (lowerState i j) q hq rfl
      refine ⟨mul_nonneg (d.embeddedTransition_nonneg i _) hw, ?_, by simp, ?_⟩
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact d.holdingMean_pos i
        · exact hpos a ha
      · change q.2.length + 1 ≤ n + 1
        have hj := j.isLt
        omega

theorem acyclicPaths_valid {s : ℕ} (d : PhaseTypeData s)
    (p : AcyclicPath) (hp : p ∈ d.acyclicPaths) :
    0 ≤ p.1 ∧ (∀ a ∈ p.2, 0 < a) ∧ p.2 ≠ [] ∧ p.2.length ≤ s := by
  obtain ⟨i, _, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  obtain ⟨hw, hpos, hne, hlen⟩ := d.acyclicPathsFrom_valid i q hq
  exact ⟨mul_nonneg (d.initial_nonneg i) hw, hpos, hne,
    hlen.trans (Nat.succ_le_of_lt i.isLt)⟩

/-- The first holding mean of a path is determined by its initial state. -/
theorem acyclicPathsFrom_head {s : ℕ} (d : PhaseTypeData s) (i : Fin s)
    (p : AcyclicPath) (hp : p ∈ d.acyclicPathsFrom i) :
    p.2.head? = some (d.holdingMean i) := by
  rw [acyclicPathsFrom, List.mem_cons] at hp
  rcases hp with rfl | hp
  · rfl
  · obtain ⟨j, _, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
    rfl

/-- Every path that visits all transient states starts at the unique top state.
Consequently all such paths have the same first holding mean. -/
theorem acyclicPaths_full_length_head {s : ℕ} (d : PhaseTypeData s)
    (top : Fin s) (htop : top.val + 1 = s) (p : AcyclicPath)
    (hp : p ∈ d.acyclicPaths) (hlen : p.2.length = s) :
    p.2.head? = some (d.holdingMean top) := by
  obtain ⟨i, _, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have hbound := (d.acyclicPathsFrom_valid i q hq).2.2.2
  have hitop : i = top := by
    apply Fin.ext
    have hi := i.isLt
    change q.2.length = s at hlen
    omega
  simpa only [hitop] using d.acyclicPathsFrom_head i q hq

end PhaseTypeData
end SSPRK
