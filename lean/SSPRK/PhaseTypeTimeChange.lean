import SSPRK.PhaseTypeAllMoments
import SSPRK.PhaseTypeThirdMoment

/-!
# Clock changes and fixed-state phase-type laws

Changing the clock rate or the initial state produces actual phase-type probability laws.
Their integral moments realize the normalized block moments used in the third-moment proof.
-/

open MeasureTheory
open scoped BigOperators

namespace SSPRK.PhaseTypeData

variable {s : ℕ} (d : PhaseTypeData s)

/-- Change only the positive uniformizing clock rate. -/
noncomputable def withRate (ν : ℝ) (hν : 0 < ν) : PhaseTypeData s :=
  { d with rate := ν, rate_pos := hν }

@[simp]
theorem withRate_rate (ν : ℝ) (hν : 0 < ν) : (d.withRate ν hν).rate = ν := rfl

@[simp]
theorem withRate_transition (ν : ℝ) (hν : 0 < ν) :
    (d.withRate ν hν).transition = d.transition := rfl

@[simp]
theorem withRate_initial (ν : ℝ) (hν : 0 < ν) : (d.withRate ν hν).initial = d.initial := rfl

@[simp]
theorem withRate_green (ν : ℝ) (hν : 0 < ν) : (d.withRate ν hν).green = d.green := rfl

@[simp]
theorem withRate_mass (ν : ℝ) (hν : 0 < ν) : (d.withRate ν hν).mass = d.mass := rfl

/-- Start in a single transient state with probability one. -/
noncomputable def startAt (i : Fin s) : PhaseTypeData s :=
  { d with
    initial := fun j ↦ if j = i then 1 else 0
    initial_nonneg := fun j ↦ by split_ifs <;> norm_num
    initial_mass_le := by simp }

@[simp]
theorem startAt_initial (i j : Fin s) : (d.startAt i).initial j = if j = i then 1 else 0 := rfl

@[simp]
theorem startAt_transition (i : Fin s) : (d.startAt i).transition = d.transition := rfl

@[simp]
theorem startAt_rate (i : Fin s) : (d.startAt i).rate = d.rate := rfl

@[simp]
theorem startAt_green (i : Fin s) : (d.startAt i).green = d.green := rfl

@[simp]
theorem startAt_mass (i : Fin s) : (d.startAt i).mass = 1 := by simp [mass]

/-- Fixed-state initialization extracts the corresponding coordinate of any vector. -/
theorem startAt_dotProduct (i : Fin s) (x : Fin s → ℝ) :
    dotProduct (d.startAt i).initial x = x i := by
  simp [dotProduct]

/-- A new clock rate appears only in the denominator of positive integral moments. -/
theorem withRate_integral_pow (ν : ℝ) (hν : 0 < ν) (k : ℕ) (hk : 0 < k) :
    ∫ x, x ^ k ∂(d.withRate ν hν).measure =
      (k.factorial : ℝ) * dotProduct d.initial ((d.green ^ k).mulVec (fun _ ↦ 1)) / ν ^ k := by
  exact (d.withRate ν hν).integral_pow_measure k hk

/-- Starting from a state extracts its factorial Green-row moment. -/
theorem startAt_integral_pow (i : Fin s) (k : ℕ) (hk : 0 < k) :
    ∫ x, x ^ k ∂(d.startAt i).measure =
      (k.factorial : ℝ) * (d.green ^ k).mulVec (fun _ ↦ 1) i / d.rate ^ k := by
  rw [(d.startAt i).integral_pow_measure k hk, d.startAt_green, d.startAt_rate,
    d.startAt_dotProduct]

/-- State initialization and a clock change give the corresponding Green-row moment. -/
theorem startAt_withRate_integral_pow (i : Fin s) (ν : ℝ) (hν : 0 < ν)
    (k : ℕ) (hk : 0 < k) :
    ∫ x, x ^ k ∂((d.startAt i).withRate ν hν).measure =
      (k.factorial : ℝ) * (d.green ^ k).mulVec (fun _ ↦ 1) i / ν ^ k := by
  rw [(d.startAt i).withRate_integral_pow ν hν k hk, d.startAt_green, d.startAt_dotProduct]

/-- The distinguished-state law at the clock rate that normalizes its Green diagonal. -/
noncomputable def normalizedStart {n : ℕ} (d : PhaseTypeData (n + 1)) : PhaseTypeData (n + 1) :=
  (d.startAt 0).withRate (d.green 0 0) d.green_pivot_pos

/-- The eliminated-state law at the same normalizing clock rate. -/
noncomputable def normalizedTail {n : ℕ} (d : PhaseTypeData (n + 1)) : PhaseTypeData n :=
  d.eliminateZero.withRate (d.green 0 0) d.green_pivot_pos

/-- Every positive integral moment of the normalized fixed-state law is its block moment. -/
theorem normalizedStart_integral_pow {n : ℕ} (d : PhaseTypeData (n + 1))
    (k : ℕ) (hk : 0 < k) :
    ∫ x, x ^ k ∂d.normalizedStart.measure = phaseBlockMoment d.normalizedGreen k := by
  rw [normalizedStart, d.startAt_withRate_integral_pow 0 _ _ k hk, phaseBlockMoment,
    d.normalizedGreen_power_row]
  simp only [div_eq_mul_inv, inv_pow]
  ring

/-- The first normalized fixed-state integral is its first block moment. -/
theorem normalizedStart_integral_one {n : ℕ} (d : PhaseTypeData (n + 1)) :
    ∫ x, x ∂d.normalizedStart.measure = phaseBlockMoment d.normalizedGreen 1 := by
  simpa only [pow_one] using d.normalizedStart_integral_pow 1 (by norm_num)

/-- The second normalized fixed-state integral is its second block moment. -/
theorem normalizedStart_integral_two {n : ℕ} (d : PhaseTypeData (n + 1)) :
    ∫ x, x ^ 2 ∂d.normalizedStart.measure = phaseBlockMoment d.normalizedGreen 2 :=
  d.normalizedStart_integral_pow 2 (by norm_num)

/-- The third normalized fixed-state integral is its third block moment. -/
theorem normalizedStart_integral_three {n : ℕ} (d : PhaseTypeData (n + 1)) :
    ∫ x, x ^ 3 ∂d.normalizedStart.measure = phaseBlockMoment d.normalizedGreen 3 :=
  d.normalizedStart_integral_pow 3 (by norm_num)

/-- The normalized eliminated law realizes the first principal-block moment. -/
theorem normalizedTail_integral_one {n : ℕ} (d : PhaseTypeData (n + 1)) :
    ∫ x, x ∂d.normalizedTail.measure = phaseBlockZ1 d.normalizedGreen := by
  have h := d.eliminateZero.withRate_integral_pow (d.green 0 0) d.green_pivot_pos 1
    (by norm_num)
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, one_mul] at h
  rw [normalizedTail, h, d.normalizedGreen_z1]
  ring

/-- The normalized eliminated law realizes the second principal-block moment. -/
theorem normalizedTail_integral_two {n : ℕ} (d : PhaseTypeData (n + 1)) :
    ∫ x, x ^ 2 ∂d.normalizedTail.measure = phaseBlockZ2 d.normalizedGreen := by
  rw [normalizedTail, d.eliminateZero.withRate_integral_pow _ _ 2 (by norm_num),
    d.normalizedGreen_z2]
  norm_num only [Nat.factorial_succ, Nat.factorial_zero]
  simp only [div_eq_mul_inv, inv_pow]
  ring

/-- The normalized eliminated law realizes the third principal-block moment. -/
theorem normalizedTail_integral_three {n : ℕ} (d : PhaseTypeData (n + 1)) :
    ∫ x, x ^ 3 ∂d.normalizedTail.measure = phaseBlockZ3 d.normalizedGreen := by
  rw [normalizedTail, d.eliminateZero.withRate_integral_pow _ _ 3 (by norm_num),
    d.normalizedGreen_z3]
  norm_num only [Nat.factorial_succ, Nat.factorial_zero]
  simp only [div_eq_mul_inv, inv_pow]
  ring

end SSPRK.PhaseTypeData
