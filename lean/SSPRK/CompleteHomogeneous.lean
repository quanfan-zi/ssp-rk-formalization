import SSPRK.CompleteHomogeneousRaising
import SSPRK.CompleteHomogeneousInequality

/-!
# Schur's inequality for normalized complete homogeneous polynomials

The proof uses the weak-composition raising identities and two finite weighted
Cauchy--Schwarz inequalities. This supplies the symmetric-polynomial inequality
cited in the paper's acyclic PH argument, including its equality case.
-/

open scoped BigOperators

namespace SSPRK

/-- The positive coordinate weights in a degree `k` composition sum to `s + k`. -/
lemma sum_composition_weights {s k : ℕ} (a : Fin s → ℕ)
    (ha : a ∈ Finset.Nat.antidiagonalTuple s k) :
    (∑ i, ((a i : ℝ) + 1)) = (s : ℝ) + k := by
  have hsum := Finset.Nat.mem_antidiagonalTuple.mp ha
  simp only [Finset.sum_add_distrib, ← Nat.cast_sum, hsum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, add_comm]

/-- Cauchy--Schwarz within one weak composition. -/
lemma compositionLinear_sq_le {s k : ℕ} (θ : Fin s → ℝ) (a : Fin s → ℕ)
    (ha : a ∈ Finset.Nat.antidiagonalTuple s k) :
    compositionLinear θ a ^ 2 ≤ ((s : ℝ) + k) * compositionQuadratic θ a := by
  simpa only [compositionLinear, compositionQuadratic, sum_composition_weights a ha] using
    finite_weighted_square_le Finset.univ (fun i ↦ (a i : ℝ) + 1) θ
      (fun i _ ↦ by positivity)

/-- Equality within a composition forces all variables to coincide. -/
lemma compositionLinear_sq_eq_iff {s k : ℕ} (hs : 0 < s) (θ : Fin s → ℝ)
    (a : Fin s → ℕ) (ha : a ∈ Finset.Nat.antidiagonalTuple s k) :
    compositionLinear θ a ^ 2 = ((s : ℝ) + k) * compositionQuadratic θ a ↔
      ∃ c : ℝ, ∀ i, θ i = c := by
  have hpos (i : Fin s) : 0 < (a i : ℝ) + 1 := by positivity
  have h := weighted_quadratic_eq_iff (fun i ↦ (a i : ℝ) + 1)
    (fun _ ↦ 1) θ (fun i ↦ θ i ^ 2) (c := 1) (d := 1) (by norm_num)
    (fun i ↦ (hpos i).le) (fun _ ↦ by norm_num) (fun _ ↦ by simp)
    (by simpa only [mul_one, sum_composition_weights a ha] using
      (show 0 < (s : ℝ) + k by positivity))
  simpa only [one_mul, mul_one, hpos, true_implies, and_self, true_and,
    eq_self, sum_composition_weights a ha, compositionLinear, compositionQuadratic] using h

/-- Schur's inequality, with the binomial normalizing constants cleared. -/
theorem completeHomogeneous_schur {s : ℕ} (hs : 0 < s) (θ : Fin s → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (k : ℕ) :
    ((k : ℝ) + 1) * ((s : ℝ) + k + 1) * completeHomogeneous θ (k + 1) ^ 2 ≤
      ((k : ℝ) + 2) * ((s : ℝ) + k) *
        completeHomogeneous θ k * completeHomogeneous θ (k + 2) := by
  have h := finite_weighted_schur (Finset.Nat.antidiagonalTuple s k)
    (compositionMonomial θ) (compositionLinear θ) (compositionQuadratic θ)
    ((s : ℝ) + k) (by positivity) (fun a _ ↦ compositionMonomial_nonneg hθ a)
    (fun a ha ↦ compositionLinear_sq_le θ a ha)
  rw [completeHomogeneous_raising, completeHomogeneous_raising_twice,
    ← completeHomogeneous] at h
  apply (mul_le_mul_iff_right₀ (show 0 < (k : ℝ) + 1 by positivity)).mp
  nlinarith only [h]

/-- Sharpness of Schur's inequality forces the variables to be equal. -/
theorem completeHomogeneous_eq_of_schur_eq {s : ℕ} (hs : 0 < s)
    (θ : Fin s → ℝ) (hθ : ∀ i, 0 ≤ θ i) (k : ℕ)
    (heq : ((k : ℝ) + 1) * ((s : ℝ) + k + 1) * completeHomogeneous θ (k + 1) ^ 2 =
      ((k : ℝ) + 2) * ((s : ℝ) + k) *
        completeHomogeneous θ k * completeHomogeneous θ (k + 2)) :
    ∃ c : ℝ, ∀ i, θ i = c := by
  by_cases hpos : ∃ i, 0 < θ i
  · have heq' : (((s : ℝ) + k) + 1) *
        (∑ a ∈ Finset.Nat.antidiagonalTuple s k,
          compositionMonomial θ a * compositionLinear θ a) ^ 2 =
        ((s : ℝ) + k) * (∑ a ∈ Finset.Nat.antidiagonalTuple s k,
          compositionMonomial θ a) * ∑ a ∈ Finset.Nat.antidiagonalTuple s k,
          compositionMonomial θ a *
            (compositionLinear θ a ^ 2 + compositionQuadratic θ a) := by
      rw [completeHomogeneous_raising, completeHomogeneous_raising_twice,
        ← completeHomogeneous]
      nlinarith only [congrArg (fun x : ℝ ↦ ((k : ℝ) + 1) * x) heq]
    have hsharp := finite_weighted_schur_eq_local (Finset.Nat.antidiagonalTuple s k)
      (compositionMonomial θ) (compositionLinear θ) (compositionQuadratic θ)
      ((s : ℝ) + k) (by positivity) (fun a _ ↦ compositionMonomial_nonneg hθ a)
      (fun a ha ↦ compositionLinear_sq_le θ a ha)
      (completeHomogeneous_pos hθ hpos k) heq'
    obtain ⟨a, ha, hwa⟩ := exists_positive_compositionMonomial hpos k
    exact (compositionLinear_sq_eq_iff hs θ a ha).mp (hsharp a ha hwa)
  · exact ⟨0, fun i ↦ le_antisymm (not_lt.mp (fun hi ↦ hpos ⟨i, hi⟩)) (hθ i)⟩

/-- Equal variables make the local first power sum constant across compositions. -/
lemma compositionLinear_of_constant {s k : ℕ} (θ : Fin s → ℝ) (c : ℝ)
    (hc : ∀ i, θ i = c) (a : Fin s → ℕ)
    (ha : a ∈ Finset.Nat.antidiagonalTuple s k) :
    compositionLinear θ a = ((s : ℝ) + k) * c := by
  simp only [compositionLinear, hc, ← Finset.sum_mul, sum_composition_weights a ha]

/-- Equal variables make the local second power sum constant across compositions. -/
lemma compositionQuadratic_of_constant {s k : ℕ} (θ : Fin s → ℝ) (c : ℝ)
    (hc : ∀ i, θ i = c) (a : Fin s → ℕ)
    (ha : a ∈ Finset.Nat.antidiagonalTuple s k) :
    compositionQuadratic θ a = ((s : ℝ) + k) * c ^ 2 := by
  simp only [compositionQuadratic, hc, ← Finset.sum_mul, sum_composition_weights a ha]

/-- Equal variables attain Schur's bound. -/
theorem completeHomogeneous_schur_eq_of_constant {s : ℕ} (θ : Fin s → ℝ)
    (c : ℝ) (hc : ∀ i, θ i = c) (k : ℕ) :
    ((k : ℝ) + 1) * ((s : ℝ) + k + 1) * completeHomogeneous θ (k + 1) ^ 2 =
      ((k : ℝ) + 2) * ((s : ℝ) + k) *
        completeHomogeneous θ k * completeHomogeneous θ (k + 2) := by
  have hfirst : ((k : ℝ) + 1) * completeHomogeneous θ (k + 1) =
      completeHomogeneous θ k * (((s : ℝ) + k) * c) := by
    rw [← completeHomogeneous_raising, completeHomogeneous, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a ha ↦ congrArg (compositionMonomial θ a * ·)
      (compositionLinear_of_constant θ c hc a ha)
  have hsecond : ((k : ℝ) + 1) * ((k : ℝ) + 2) * completeHomogeneous θ (k + 2) =
      completeHomogeneous θ k * ((((s : ℝ) + k) * c) ^ 2 + ((s : ℝ) + k) * c ^ 2) := by
    rw [← completeHomogeneous_raising_twice, completeHomogeneous, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a ha ↦ by
      rw [compositionLinear_of_constant θ c hc a ha,
        compositionQuadratic_of_constant θ c hc a ha]
  have hmain : ((s : ℝ) + k + 1) *
      (((k : ℝ) + 1) * completeHomogeneous θ (k + 1)) ^ 2 =
      ((s : ℝ) + k) * completeHomogeneous θ k *
        (((k : ℝ) + 1) * ((k : ℝ) + 2) * completeHomogeneous θ (k + 2)) := by
    rw [hfirst, hsecond]
    ring
  apply mul_left_cancel₀ (show (k : ℝ) + 1 ≠ 0 by positivity)
  nlinarith only [hmain]

/-- Equality in the normalized complete-homogeneous inequality is exactly equal variables. -/
theorem completeHomogeneous_schur_eq_iff {s : ℕ} (hs : 0 < s) (θ : Fin s → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (k : ℕ) :
    (((k : ℝ) + 1) * ((s : ℝ) + k + 1) * completeHomogeneous θ (k + 1) ^ 2 =
      ((k : ℝ) + 2) * ((s : ℝ) + k) *
        completeHomogeneous θ k * completeHomogeneous θ (k + 2)) ↔
      ∃ c : ℝ, ∀ i, θ i = c :=
  ⟨completeHomogeneous_eq_of_schur_eq hs θ hθ k,
    fun ⟨c, hc⟩ ↦ completeHomogeneous_schur_eq_of_constant θ c hc k⟩

/-- Schur's bound after restoring the factorials in exponential-sum moments. -/
theorem completeHomogeneous_factorial_schur {s : ℕ} (hs : 0 < s) (θ : Fin s → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (k : ℕ) :
    ((s : ℝ) + k + 1) * ((Nat.factorial (k + 1) : ℝ) *
      completeHomogeneous θ (k + 1)) ^ 2 ≤
      ((s : ℝ) + k) * ((Nat.factorial k : ℝ) * completeHomogeneous θ k) *
        ((Nat.factorial (k + 2) : ℝ) * completeHomogeneous θ (k + 2)) := by
  have h := mul_le_mul_of_nonneg_left (completeHomogeneous_schur hs θ hθ k)
    (show 0 ≤ ((k : ℝ) + 1) * (Nat.factorial k : ℝ) ^ 2 by positivity)
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  nlinarith only [h]

/-- The factorial moment version has the same equality cases. -/
theorem completeHomogeneous_factorial_schur_eq_iff {s : ℕ} (hs : 0 < s)
    (θ : Fin s → ℝ) (hθ : ∀ i, 0 ≤ θ i) (k : ℕ) :
    (((s : ℝ) + k + 1) * ((Nat.factorial (k + 1) : ℝ) *
      completeHomogeneous θ (k + 1)) ^ 2 =
      ((s : ℝ) + k) * ((Nat.factorial k : ℝ) * completeHomogeneous θ k) *
        ((Nat.factorial (k + 2) : ℝ) * completeHomogeneous θ (k + 2))) ↔
      ∃ c : ℝ, ∀ i, θ i = c := by
  rw [← completeHomogeneous_schur_eq_iff hs θ hθ k]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  constructor
  · intro heq
    apply mul_left_cancel₀ (show ((k : ℝ) + 1) * (Nat.factorial k : ℝ) ^ 2 ≠ 0 by positivity)
    nlinarith only [heq]
  · intro heq
    nlinarith only [congrArg (fun x : ℝ ↦ ((k : ℝ) + 1) *
      (Nat.factorial k : ℝ) ^ 2 * x) heq]

end SSPRK
