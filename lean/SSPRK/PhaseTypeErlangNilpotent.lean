import SSPRK.PhaseTypeErlangCharpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Nilpotence of the centered Erlang phase-type generator

If an `s`-phase generator has characteristic polynomial `(X + κ) ^ s`, then
shifting the generator by `κ` gives a nilpotent matrix. The generator's
off-diagonal nonnegativity and the vanishing trace of the square of this shift
then force every diagonal entry of the shift to vanish.
-/

open scoped BigOperators Polynomial

namespace SSPRK
namespace PhaseTypeData

noncomputable section

/-- The generator shifted by the Erlang rate. -/
def erlangShift {s : ℕ} (d : PhaseTypeData s) (κ : ℝ) :
    Matrix (Fin s) (Fin s) ℝ :=
  d.generator + κ • 1

/-- Cayley--Hamilton identifies the nilpotence exponent of the shifted generator. -/
theorem erlangShift_pow_eq_zero {s : ℕ} (d : PhaseTypeData s) (κ : ℝ)
    (hchar : d.generator.charpoly = (Polynomial.X + Polynomial.C κ) ^ s) :
    d.erlangShift κ ^ s = 0 := by
  have hcayley := d.generator.aeval_self_charpoly
  rw [hchar] at hcayley
  simpa [erlangShift, Algebra.algebraMap_eq_smul_one] using hcayley

/-- The generator shifted by the Erlang rate is nilpotent. -/
theorem erlangShift_isNilpotent {s : ℕ} (d : PhaseTypeData s) (κ : ℝ)
    (hchar : d.generator.charpoly = (Polynomial.X + Polynomial.C κ) ^ s) :
    IsNilpotent (d.erlangShift κ) :=
  ⟨s, d.erlangShift_pow_eq_zero κ hchar⟩

private lemma diag_eq_zero_of_isNilpotent_of_offdiag_nonneg {s : ℕ}
    (H : Matrix (Fin s) (Fin s) ℝ) (hnil : IsNilpotent H)
    (hoffdiag : ∀ i j, i ≠ j → 0 ≤ H i j) (i : Fin s) :
    H i i = 0 := by
  have hsq_nil : IsNilpotent (H ^ 2) := hnil.pow_of_pos (by omega)
  have htrace : Matrix.trace (H ^ 2) = 0 :=
    (Matrix.isNilpotent_trace_of_isNilpotent hsq_nil).eq_zero
  have hterm_nonneg : ∀ i j, 0 ≤ H i j * H j i := by
    intro i j
    by_cases hij : i = j
    · subst j
      exact mul_self_nonneg _
    · exact mul_nonneg (hoffdiag i j hij) (hoffdiag j i (Ne.symm hij))
  have hdiag_nonneg : ∀ j, 0 ≤ (H ^ 2) j j := by
    intro j
    rw [pow_two, Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ ↦ hterm_nonneg j k
  have hdiag_zero : ∀ j, (H ^ 2) j j = 0 := by
    intro j
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ ↦ hdiag_nonneg k)).mp htrace
      j (Finset.mem_univ j)
  have hsum_zero : ∑ j, H i j * H j i = 0 := by
    simpa [pow_two, Matrix.mul_apply] using hdiag_zero i
  have hii_mul_zero :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ hterm_nonneg i j)).mp hsum_zero
      i (Finset.mem_univ i)
  exact mul_self_eq_zero.mp hii_mul_zero

/-- Every diagonal generator entry equals the negative Erlang rate. -/
theorem generator_diag_eq_neg_of_charpoly_eq {s : ℕ} (d : PhaseTypeData s) (κ : ℝ)
    (hchar : d.generator.charpoly = (Polynomial.X + Polynomial.C κ) ^ s) (i : Fin s) :
    d.generator i i = -κ := by
  have hoffdiag : ∀ i j, i ≠ j → 0 ≤ d.erlangShift κ i j := by
    intro i j hij
    simp [erlangShift, generator, hij,
      mul_nonneg d.rate_pos.le (d.substochastic.nonneg i j)]
  have hdiag := diag_eq_zero_of_isNilpotent_of_offdiag_nonneg
    (d.erlangShift κ) (d.erlangShift_isNilpotent κ hchar) hoffdiag i
  simpa [erlangShift] using eq_neg_of_add_eq_zero_left hdiag

/-- The generator shifted by the Erlang rate is entrywise nonnegative. -/
theorem erlangShift_nonneg {s : ℕ} (d : PhaseTypeData s) (κ : ℝ)
    (hchar : d.generator.charpoly = (Polynomial.X + Polynomial.C κ) ^ s) :
    ∀ i j, 0 ≤ d.erlangShift κ i j := by
  intro i j
  by_cases hij : i = j
  · subst j
    rw [show d.erlangShift κ i i = 0 by
      simpa [erlangShift] using
        congrArg (fun x : ℝ ↦ x + κ) (d.generator_diag_eq_neg_of_charpoly_eq κ hchar i)]
  · simp [erlangShift, generator, hij,
      mul_nonneg d.rate_pos.le (d.substochastic.nonneg i j)]

/-- All centered-generator conclusions forced by an Erlang characteristic polynomial. -/
theorem erlangShift_properties {s : ℕ} (d : PhaseTypeData s) (κ : ℝ)
    (_hs : 0 < s) (_hκ : 0 < κ)
    (hchar : d.generator.charpoly = (Polynomial.X + Polynomial.C κ) ^ s) :
    d.erlangShift κ ^ s = 0 ∧
      IsNilpotent (d.erlangShift κ) ∧
      (∀ i j, 0 ≤ d.erlangShift κ i j) ∧
      ∀ i, d.generator i i = -κ := by
  exact ⟨d.erlangShift_pow_eq_zero κ hchar, d.erlangShift_isNilpotent κ hchar,
    d.erlangShift_nonneg κ hchar, d.generator_diag_eq_neg_of_charpoly_eq κ hchar⟩

end

end PhaseTypeData
end SSPRK
