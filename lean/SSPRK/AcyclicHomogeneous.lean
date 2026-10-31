import SSPRK.AcyclicPaths
import SSPRK.CompleteHomogeneousRecurrence

/-!
# Complete homogeneous polynomials in the finite path expansion

The recursive holding-time polynomial is the complete homogeneous polynomial of
the list of holding means. This is the moment-polynomial identity used in V2.10.
-/

namespace SSPRK

theorem list_getElem_cons_eq (a : ℝ) (as : List ℝ) :
    (fun i : Fin (a :: as).length ↦ (a :: as)[i.val]) =
      Fin.cons a (fun i : Fin as.length ↦ as[i.val]) := by
  funext i
  exact Fin.cases rfl (fun j ↦ rfl) i

/-- The recursive path polynomial is the complete homogeneous symmetric polynomial. -/
theorem pathPolynomial_eq_completeHomogeneous (as : List ℝ) (k : ℕ) :
    pathPolynomial as k = completeHomogeneous (fun i : Fin as.length ↦ as[i.val]) k := by
  induction k generalizing as with
  | zero => simp
  | succ k ih =>
    induction as with
    | nil => simp
    | cons a as ihlist =>
      rw [pathPolynomial_cons_succ, ih, ihlist, list_getElem_cons_eq,
        completeHomogeneous_cons_succ]

theorem pathPolynomial_pos (as : List ℝ) (hne : as ≠ [])
    (hpos : ∀ a ∈ as, 0 < a) (k : ℕ) : 0 < pathPolynomial as k := by
  rw [pathPolynomial_eq_completeHomogeneous]
  apply completeHomogeneous_pos (fun i ↦ (hpos _ (List.getElem_mem i.isLt)).le)
  cases as with
  | nil => exact (hne rfl).elim
  | cons a as => exact ⟨0, hpos a List.mem_cons_self⟩

theorem pathPolynomial_one_const (as : List ℝ) (c : ℝ)
    (hc : ∀ a ∈ as, a = c) : pathPolynomial as 1 = (as.length : ℝ) * c := by
  induction as with
  | nil => simp
  | cons a as ih =>
    rw [pathPolynomial_cons_succ, pathPolynomial_zero,
      ih (fun b hb ↦ hc b (List.mem_cons_of_mem a hb)), hc a List.mem_cons_self]
    simp [Nat.cast_add, Nat.cast_one, add_mul, add_comm]

theorem pathPolynomial_two_const (as : List ℝ) (c : ℝ)
    (hc : ∀ a ∈ as, a = c) :
    pathPolynomial as 2 = (as.length : ℝ) * (as.length + 1) / 2 * c ^ 2 := by
  induction as with
  | nil => simp
  | cons a as ih =>
    rw [pathPolynomial_cons_succ, pathPolynomial_one_const (a :: as) c hc,
      ih (fun b hb ↦ hc b (List.mem_cons_of_mem a hb)), hc a List.mem_cons_self]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

end SSPRK
