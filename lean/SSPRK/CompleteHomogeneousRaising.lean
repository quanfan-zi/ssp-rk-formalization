import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic

/-!
# Complete homogeneous polynomials and raising weak compositions

The two raising identities count the same monomials after increasing one coordinate.
They provide the finite-sum identities used in the proof of Schur's inequality.
-/

open scoped BigOperators

namespace SSPRK

/-- The monomial belonging to a weak composition. -/
noncomputable def compositionMonomial {s : ℕ} (θ : Fin s → ℝ) (a : Fin s → ℕ) : ℝ :=
  ∏ i, θ i ^ a i

/-- The degree `k` complete homogeneous symmetric polynomial evaluated at `θ`. -/
noncomputable def completeHomogeneous {s : ℕ} (θ : Fin s → ℝ) (k : ℕ) : ℝ :=
  ∑ a ∈ Finset.Nat.antidiagonalTuple s k, compositionMonomial θ a

/-- Weighted first power sum associated to a weak composition. -/
noncomputable def compositionLinear {s : ℕ} (θ : Fin s → ℝ) (a : Fin s → ℕ) : ℝ :=
  ∑ i, ((a i : ℝ) + 1) * θ i

/-- Weighted second power sum associated to a weak composition. -/
noncomputable def compositionQuadratic {s : ℕ} (θ : Fin s → ℝ) (a : Fin s → ℕ) : ℝ :=
  ∑ i, ((a i : ℝ) + 1) * θ i ^ 2

@[simp] theorem completeHomogeneous_zero {s : ℕ} (θ : Fin s → ℝ) :
    completeHomogeneous θ 0 = 1 := by
  simp [completeHomogeneous, Finset.Nat.antidiagonalTuple_zero_right, compositionMonomial]

theorem compositionMonomial_nonneg {s : ℕ} {θ : Fin s → ℝ} (hθ : ∀ i, 0 ≤ θ i)
    (a : Fin s → ℕ) : 0 ≤ compositionMonomial θ a :=
  Finset.prod_nonneg fun i _ ↦ pow_nonneg (hθ i) _

theorem completeHomogeneous_nonneg {s : ℕ} {θ : Fin s → ℝ} (hθ : ∀ i, 0 ≤ θ i)
    (k : ℕ) : 0 ≤ completeHomogeneous θ k :=
  Finset.sum_nonneg fun a _ ↦ compositionMonomial_nonneg hθ a

/-- A positive coordinate supplies a positive monomial at every degree. -/
theorem exists_positive_compositionMonomial {s : ℕ} {θ : Fin s → ℝ}
    (hθ : ∃ i, 0 < θ i) (k : ℕ) :
    ∃ a ∈ Finset.Nat.antidiagonalTuple s k, 0 < compositionMonomial θ a := by
  classical
  obtain ⟨i, hi⟩ := hθ
  let a : Fin s → ℕ := fun j ↦ if j = i then k else 0
  have ha : a ∈ Finset.Nat.antidiagonalTuple s k := by
    simp [Finset.Nat.mem_antidiagonalTuple, a]
  have hm : compositionMonomial θ a = θ i ^ k := by
    calc
      _ = θ i ^ a i := Finset.prod_eq_single i
        (fun j _ hji ↦ by simp [a, hji]) (by simp)
      _ = _ := by simp [a]
  exact ⟨a, ha, hm ▸ pow_pos hi k⟩

theorem completeHomogeneous_pos {s : ℕ} {θ : Fin s → ℝ} (hθ : ∀ i, 0 ≤ θ i)
    (hpos : ∃ i, 0 < θ i) (k : ℕ) : 0 < completeHomogeneous θ k := by
  obtain ⟨a, ha, hapos⟩ := exists_positive_compositionMonomial hpos k
  exact lt_of_lt_of_le hapos
    (Finset.single_le_sum (fun b _ ↦ compositionMonomial_nonneg hθ b) ha)

private lemma sum_update_succ {s : ℕ} (a : Fin s → ℕ) (i : Fin s) :
    (∑ j, Function.update a i (a i + 1) j) = (∑ j, a j) + 1 := by
  have h := Finset.sum_update_of_mem (Finset.mem_univ i) a (a i + 1)
  have h' := Finset.sum_erase_add Finset.univ a (Finset.mem_univ i)
  simp only [Finset.sdiff_singleton_eq_erase] at h
  omega

private lemma update_succ_mem {s k : ℕ} {a : Fin s → ℕ}
    (ha : a ∈ Finset.Nat.antidiagonalTuple s k) (i : Fin s) :
    Function.update a i (a i + 1) ∈ Finset.Nat.antidiagonalTuple s (k + 1) := by
  simp only [Finset.Nat.mem_antidiagonalTuple, sum_update_succ,
    Finset.Nat.mem_antidiagonalTuple.mp ha]

private lemma raising_one_coordinate {s : ℕ} (k : ℕ) (i : Fin s)
    (f : (Fin s → ℕ) → ℝ) :
    (∑ a ∈ Finset.Nat.antidiagonalTuple s k,
      ((a i : ℝ) + 1) * f (Function.update a i (a i + 1))) =
      ∑ b ∈ (Finset.Nat.antidiagonalTuple s (k + 1)).filter (fun b ↦ 0 < b i),
        (b i : ℝ) * f b := by
  classical
  refine Finset.sum_bij (fun a _ ↦ Function.update a i (a i + 1)) ?_ ?_ ?_ ?_
  · intro a ha
    exact Finset.mem_filter.mpr ⟨update_succ_mem ha i, by simp⟩
  · intro a ha b hb hab
    ext j
    by_cases hji : j = i
    · subst j
      have h := congrFun hab i
      simpa using h
    · have h := congrFun hab j
      simpa [Function.update_of_ne hji] using h
  · intro b hb
    have hbi : 1 ≤ b i := (Finset.mem_filter.mp hb).2
    let a := Function.update b i (b i - 1)
    have hrecover : Function.update a i (a i + 1) = b := by
      simp [a, Nat.sub_add_cancel hbi]
    have ha : a ∈ Finset.Nat.antidiagonalTuple s k := by
      apply Finset.Nat.mem_antidiagonalTuple.mpr
      have hsum := sum_update_succ a i
      rw [hrecover, Finset.Nat.mem_antidiagonalTuple.mp (Finset.mem_filter.mp hb).1] at hsum
      omega
    exact ⟨a, ha, hrecover⟩
  · intro a ha
    simp

/-- Raising one coordinate counts each next-degree composition by its total degree. -/
theorem sum_composition_raise {s : ℕ} (k : ℕ) (f : (Fin s → ℕ) → ℝ) :
    (∑ a ∈ Finset.Nat.antidiagonalTuple s k,
      ∑ i, ((a i : ℝ) + 1) * f (Function.update a i (a i + 1))) =
      ((k : ℝ) + 1) * ∑ b ∈ Finset.Nat.antidiagonalTuple s (k + 1), f b := by
  classical
  rw [Finset.sum_comm]
  have hfixed (i : Fin s) :
      (∑ a ∈ Finset.Nat.antidiagonalTuple s k,
        ((a i : ℝ) + 1) * f (Function.update a i (a i + 1))) =
        ∑ b ∈ Finset.Nat.antidiagonalTuple s (k + 1), (b i : ℝ) * f b := by
    rw [raising_one_coordinate]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro b hb hnot
    have hz : b i = 0 := by simpa [hb] using hnot
    simp [hz]
  simp_rw [hfixed]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← Finset.sum_mul, ← Nat.cast_sum, Finset.Nat.mem_antidiagonalTuple.mp hb]
  simp

theorem compositionMonomial_update_succ {s : ℕ} (θ : Fin s → ℝ) (a : Fin s → ℕ)
    (i : Fin s) :
    compositionMonomial θ (Function.update a i (a i + 1)) =
      compositionMonomial θ a * θ i := by
  classical
  have hf : (fun j ↦ θ j ^ Function.update a i (a i + 1) j) =
      (fun j ↦ θ j ^ a j * (if j = i then θ i else 1)) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [pow_succ]
    · simp [hji]
  unfold compositionMonomial
  rw [hf, Finset.prod_mul_distrib]
  simp

theorem compositionLinear_update_succ {s : ℕ} (θ : Fin s → ℝ) (a : Fin s → ℕ)
    (i : Fin s) :
    compositionLinear θ (Function.update a i (a i + 1)) =
      compositionLinear θ a + θ i := by
  classical
  have hf : (fun j ↦ ((Function.update a i (a i + 1) j : ℝ) + 1) * θ j) =
      (fun j ↦ ((a j : ℝ) + 1) * θ j + (if j = i then θ i else 0)) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self, Nat.cast_add, Nat.cast_one, ↓reduceIte]
      ring
    · simp [hji]
  unfold compositionLinear
  rw [hf, Finset.sum_add_distrib]
  simp

/-- The first raising identity for complete homogeneous symmetric polynomials. -/
theorem completeHomogeneous_raising {s : ℕ} (θ : Fin s → ℝ) (k : ℕ) :
    (∑ a ∈ Finset.Nat.antidiagonalTuple s k,
      compositionMonomial θ a * compositionLinear θ a) =
      ((k : ℝ) + 1) * completeHomogeneous θ (k + 1) := by
  calc
    _ = ∑ a ∈ Finset.Nat.antidiagonalTuple s k,
        ∑ i, ((a i : ℝ) + 1) * compositionMonomial θ (Function.update a i (a i + 1)) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [compositionLinear, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [compositionMonomial_update_succ]
      ring
    _ = _ := sum_composition_raise k (compositionMonomial θ)

/-- The second raising identity, including the diagonal correction from repeated increments. -/
theorem completeHomogeneous_raising_twice {s : ℕ} (θ : Fin s → ℝ) (k : ℕ) :
    (∑ a ∈ Finset.Nat.antidiagonalTuple s k,
      compositionMonomial θ a * (compositionLinear θ a ^ 2 + compositionQuadratic θ a)) =
      ((k : ℝ) + 1) * ((k : ℝ) + 2) * completeHomogeneous θ (k + 2) := by
  have hlocal (a : Fin s → ℕ) :
      (∑ i, ((a i : ℝ) + 1) *
        (compositionMonomial θ (Function.update a i (a i + 1)) *
          compositionLinear θ (Function.update a i (a i + 1)))) =
        compositionMonomial θ a *
          (compositionLinear θ a ^ 2 + compositionQuadratic θ a) := by
    simp_rw [compositionMonomial_update_succ, compositionLinear_update_succ]
    calc
      _ = ∑ i, (compositionMonomial θ a * compositionLinear θ a *
          (((a i : ℝ) + 1) * θ i) +
          compositionMonomial θ a * (((a i : ℝ) + 1) * θ i ^ 2)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        change compositionMonomial θ a * compositionLinear θ a * compositionLinear θ a +
          compositionMonomial θ a * compositionQuadratic θ a = _
        ring
  calc
    _ = ∑ a ∈ Finset.Nat.antidiagonalTuple s k,
        ∑ i, ((a i : ℝ) + 1) *
          (compositionMonomial θ (Function.update a i (a i + 1)) *
            compositionLinear θ (Function.update a i (a i + 1))) := by
      exact Finset.sum_congr rfl fun a _ ↦ (hlocal a).symm
    _ = ((k : ℝ) + 1) * ∑ b ∈ Finset.Nat.antidiagonalTuple s (k + 1),
        compositionMonomial θ b * compositionLinear θ b :=
      sum_composition_raise k (fun a ↦ compositionMonomial θ a * compositionLinear θ a)
    _ = _ := by
      rw [completeHomogeneous_raising]
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_assoc]
      ring

end SSPRK
