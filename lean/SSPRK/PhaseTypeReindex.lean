import SSPRK.PhaseType

/-!
# Reindexing finite phase-type representations

Relabeling the transient states preserves the generator, initial mass, absorption weights,
and the resulting probability measure up to the same simultaneous matrix reindexing.
-/

open scoped BigOperators

namespace SSPRK.PhaseTypeData

variable {s : ℕ}

/-- Relabel the transient states of a phase-type representation. -/
noncomputable def reindex (d : PhaseTypeData s) (e : Fin s ≃ Fin s) : PhaseTypeData s where
  transition := d.transition.submatrix e e
  initial := d.initial ∘ e
  rate := d.rate
  rate_pos := d.rate_pos
  substochastic := by
    constructor
    · intro i j
      exact d.substochastic.nonneg (e i) (e j)
    · intro i
      change ∑ j, d.transition (e i) (e j) ≤ 1
      rw [e.sum_comp]
      exact d.substochastic.row_sum_le (e i)
  transient := by
    rw [show 1 - d.transition.submatrix e e = (1 - d.transition).submatrix e e by
      ext i j
      simp [Matrix.one_apply]]
    simpa only [Matrix.det_submatrix_equiv_self] using d.transient
  initial_nonneg := fun i ↦ d.initial_nonneg (e i)
  initial_mass_le := by
    change ∑ i, d.initial (e i) ≤ 1
    rw [e.sum_comp]
    exact d.initial_mass_le

/-- Reindexing simultaneously permutes the rows and columns of the generator. -/
@[simp]
theorem generator_reindex (d : PhaseTypeData s) (e : Fin s ≃ Fin s) :
    (d.reindex e).generator = d.generator.submatrix e e := by
  ext i j
  simp [generator, reindex, Matrix.one_apply]

/-- Reindexing preserves the initial transient mass. -/
@[simp]
theorem mass_reindex (d : PhaseTypeData s) (e : Fin s ≃ Fin s) :
    (d.reindex e).mass = d.mass := by
  unfold mass
  change ∑ i, d.initial (e i) = ∑ i, d.initial i
  exact e.sum_comp d.initial

/-- Matrix powers commute with simultaneous reindexing. -/
@[simp]
theorem transition_pow_reindex (d : PhaseTypeData s) (e : Fin s ≃ Fin s) (n : ℕ) :
    (d.reindex e).transition ^ n = (d.transition ^ n).submatrix e e := by
  change (d.transition.submatrix e e) ^ n = (d.transition ^ n).submatrix e e
  induction n with
  | zero => exact (Matrix.submatrix_one_equiv e).symm
  | succ n ih =>
      rw [pow_succ, pow_succ, ih]
      exact Matrix.submatrix_mul_equiv (d.transition ^ n) d.transition e e e

/-- Reindexing permutes the exit vector. -/
@[simp]
theorem exit_reindex (d : PhaseTypeData s) (e : Fin s ≃ Fin s) :
    (d.reindex e).exit = d.exit ∘ e := by
  rw [exit, exit]
  change (1 - d.transition.submatrix e e).mulVec (fun _ ↦ 1) = _
  rw [show 1 - d.transition.submatrix e e = (1 - d.transition).submatrix e e by
    ext i j
    simp [Matrix.one_apply]]
  rw [Matrix.submatrix_mulVec_equiv]
  rfl

/-- Reindexing preserves every discrete absorption weight. -/
@[simp]
theorem weight_reindex (d : PhaseTypeData s) (e : Fin s ≃ Fin s) (n : ℕ) :
    (d.reindex e).weight n = d.weight n := by
  rw [weight, weight, transition_pow_reindex, exit_reindex,
    Matrix.submatrix_mulVec_equiv]
  rw [show (d.exit ∘ e) ∘ e.symm = d.exit by
    ext i
    simp]
  simp only [reindex]
  unfold dotProduct
  simp only [Function.comp_apply]
  exact e.sum_comp (fun i ↦ d.initial i * (d.transition ^ n).mulVec d.exit i)

/-- Reindexing preserves the positive-time part of the phase-type law. -/
@[simp]
theorem positiveMeasure_reindex (d : PhaseTypeData s) (e : Fin s ≃ Fin s) :
    (d.reindex e).positiveMeasure = d.positiveMeasure := by
  unfold positiveMeasure
  congr 1
  funext n
  rw [weight_reindex]
  rfl

/-- Reindexing the transient states does not change the represented probability measure. -/
@[simp]
theorem measure_reindex (d : PhaseTypeData s) (e : Fin s ≃ Fin s) :
    (d.reindex e).measure = d.measure := by
  rw [measure, measure, mass_reindex, positiveMeasure_reindex]

end SSPRK.PhaseTypeData
