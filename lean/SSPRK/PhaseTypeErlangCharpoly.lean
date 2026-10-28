import SSPRK.PhaseTypeLaplaceGenerator
import SSPRK.ErlangLaplace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Div

/-!
# Characteristic-polynomial obstruction for Erlang phase-type laws

This is the pole-counting first step of historical V1.6 Lemma 4.7.  The generator resolvent is
written using its adjugate and determinant; equality with the Erlang Laplace transform
then gives a polynomial identity on the nonnegative half-line.
-/

open MeasureTheory
open scoped BigOperators Polynomial

namespace SSPRK
namespace PhaseTypeData

noncomputable section

/-- The polynomial numerator in the adjugate form of the generator resolvent. -/
def generatorLaplaceNumerator {m : ℕ} (d : PhaseTypeData m) : ℝ[X] :=
  dotProduct (fun i ↦ Polynomial.C (d.initial i))
    (d.generator.charmatrix.adjugate.mulVec
      (fun i ↦ Polynomial.C ((-d.generator).mulVec (fun _ ↦ 1) i)))

/-- Evaluating the polynomial numerator evaluates the adjugate resolvent matrix. -/
theorem eval_generatorLaplaceNumerator {m : ℕ} (d : PhaseTypeData m) (u : ℝ) :
    d.generatorLaplaceNumerator.eval u = dotProduct d.initial
      ((u • (1 : Matrix (Fin m) (Fin m) ℝ) - d.generator).adjugate.mulVec
        ((-d.generator).mulVec (fun _ ↦ 1))) := by
  have hmatrix : (Polynomial.evalRingHom u).mapMatrix d.generator.charmatrix =
      u • (1 : Matrix (Fin m) (Fin m) ℝ) - d.generator := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.charmatrix, Matrix.scalar, hij]
  have hadj : (Polynomial.evalRingHom u).mapMatrix d.generator.charmatrix.adjugate =
      (u • (1 : Matrix (Fin m) (Fin m) ℝ) - d.generator).adjugate := by
    rw [RingHom.map_adjugate, hmatrix]
  change (Polynomial.evalRingHom u) d.generatorLaplaceNumerator = _
  simp only [generatorLaplaceNumerator, dotProduct, Matrix.mulVec, map_sum, map_mul, map_one]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (Polynomial.evalRingHom u) (Polynomial.C (d.initial i)) = d.initial i by simp]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hadj_ij := congrArg (fun M : Matrix (Fin m) (Fin m) ℝ ↦ M i j) hadj
  change (Polynomial.evalRingHom u) (d.generator.charmatrix.adjugate i j) = _ at hadj_ij
  rw [hadj_ij]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp

/-- Clearing the nonsingular resolvent denominator produces the polynomial numerator. -/
theorem det_mul_generator_resolvent {m : ℕ} (d : PhaseTypeData m) (u : ℝ)
    (hu : 0 ≤ u) :
    (u • (1 : Matrix (Fin m) (Fin m) ℝ) - d.generator).det *
      dotProduct d.initial
        ((u • (1 : Matrix (Fin m) (Fin m) ℝ) - d.generator)⁻¹.mulVec
          ((-d.generator).mulVec (fun _ ↦ 1))) =
      d.generatorLaplaceNumerator.eval u := by
  let Q := u • (1 : Matrix (Fin m) (Fin m) ℝ) - d.generator
  have hdet : Q.det ≠ 0 := d.laplace_shift_det_ne_zero u hu
  rw [d.eval_generatorLaplaceNumerator]
  change Q.det * dotProduct d.initial (Q⁻¹.mulVec ((-d.generator).mulVec (fun _ ↦ 1))) = _
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_mulVec, dotProduct_smul]
  simp only [smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hdet, one_mul]

/-- The generator characteristic polynomial evaluates to the shifted determinant. -/
theorem eval_generator_charpoly {m : ℕ} (d : PhaseTypeData m) (u : ℝ) :
    d.generator.charpoly.eval u =
      (u • (1 : Matrix (Fin m) (Fin m) ℝ) - d.generator).det := by
  rw [Matrix.eval_charpoly]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [Matrix.scalar, hij]

/-- Equality with an Erlang law gives the polynomial identity obtained by clearing poles. -/
theorem erlang_generator_charpoly_identity {m s : ℕ} (d : PhaseTypeData m) (κ : ℝ)
    (hs : 0 < s) (hκ : 0 < κ) (hmass : d.mass = 1)
    (hlaw : d.measure = ProbabilityTheory.gammaMeasure (s : ℝ) κ) :
    Polynomial.C (κ ^ s) * d.generator.charpoly =
      d.generatorLaplaceNumerator * (Polynomial.X + Polynomial.C κ) ^ s := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ici_infinite (0 : ℝ)).mono
  intro u hu
  change 0 ≤ u at hu
  simp only [Set.mem_setOf_eq, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X]
  have hlaplace := d.integral_exp_neg_mul_eq_generator u hu
  rw [hlaw, integral_exp_neg_mul_gammaMeasure (Nat.cast_pos.mpr hs) hκ hu,
    Real.rpow_natCast, hmass] at hlaplace
  simp only [sub_self, zero_add] at hlaplace
  have hclear := d.det_mul_generator_resolvent u hu
  rw [← hlaplace] at hclear
  rw [d.eval_generator_charpoly, ← hclear]
  have hdenom : κ + u ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hκ hu)
  rw [div_pow]
  field_simp [hdenom]
  ring

/-- The Erlang pole of order `s` forces the corresponding characteristic-polynomial factor. -/
theorem erlang_factor_dvd_generator_charpoly {m s : ℕ} (d : PhaseTypeData m) (κ : ℝ)
    (hs : 0 < s) (hκ : 0 < κ) (hmass : d.mass = 1)
    (hlaw : d.measure = ProbabilityTheory.gammaMeasure (s : ℝ) κ) :
    (Polynomial.X + Polynomial.C κ) ^ s ∣ d.generator.charpoly := by
  have hid := d.erlang_generator_charpoly_identity κ hs hκ hmass hlaw
  have hcunit : IsUnit (Polynomial.C (κ ^ s) : ℝ[X]) := by
    rw [Polynomial.isUnit_C, isUnit_iff_ne_zero]
    exact pow_ne_zero s hκ.ne'
  apply hcunit.dvd_mul_left.mp
  exact ⟨d.generatorLaplaceNumerator, by simpa [mul_comm] using hid⟩

/-- An `s`-stage Erlang law needs at least `s` transient phases in any PH representation. -/
theorem erlang_shape_le_num_phases {m s : ℕ} (d : PhaseTypeData m) (κ : ℝ)
    (hs : 0 < s) (hκ : 0 < κ) (hmass : d.mass = 1)
    (hlaw : d.measure = ProbabilityTheory.gammaMeasure (s : ℝ) κ) : s ≤ m := by
  have hdvd := d.erlang_factor_dvd_generator_charpoly κ hs hκ hmass hlaw
  have hdegree := Polynomial.natDegree_le_of_dvd hdvd d.generator.charpoly_monic.ne_zero
  simpa [Polynomial.natDegree_pow, Matrix.charpoly_natDegree_eq_dim] using hdegree

/-- With at most `s` phases, the phase count and characteristic polynomial are forced. -/
theorem eq_num_phases_and_charpoly_of_le_erlang_shape {m s : ℕ}
    (d : PhaseTypeData m) (κ : ℝ) (hs : 0 < s) (hκ : 0 < κ)
    (hmass : d.mass = 1)
    (hlaw : d.measure = ProbabilityTheory.gammaMeasure (s : ℝ) κ)
    (hm : m ≤ s) :
    m = s ∧ d.generator.charpoly = (Polynomial.X + Polynomial.C κ) ^ s := by
  have hs_le_m := d.erlang_shape_le_num_phases κ hs hκ hmass hlaw
  refine ⟨le_antisymm hm hs_le_m, ?_⟩
  have hdvd := d.erlang_factor_dvd_generator_charpoly κ hs hκ hmass hlaw
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
  · exact (Polynomial.monic_X_add_C κ).pow s
  · exact d.generator.charpoly_monic
  · exact hdvd
  · simpa [Polynomial.natDegree_pow, Matrix.charpoly_natDegree_eq_dim] using hm

end

end PhaseTypeData
end SSPRK
