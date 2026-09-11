import SSPRK.Substochastic

/-!
# Uniformized finite phase-type representations

`PhaseTypeData` specifies a finite transient block, an initial subprobability row and a
positive clock rate. Its continuous-time transient generator is `rate • (transition - 1)`.
The missing initial mass is an atom at zero. The probability measure and its integral
moment identities are constructed in the subsequent modules.
-/

open scoped BigOperators

namespace SSPRK

/-- A uniformized representation, allowing immediate absorption and cyclic transitions. -/
structure PhaseTypeData (s : ℕ) where
  transition : Matrix (Fin s) (Fin s) ℝ
  initial : Fin s → ℝ
  rate : ℝ
  rate_pos : 0 < rate
  substochastic : Substochastic transition
  transient : (1 - transition).det ≠ 0
  initial_nonneg : ∀ i, 0 ≤ initial i
  initial_mass_le : ∑ i, initial i ≤ 1

namespace PhaseTypeData

/-- Initial mass assigned to the transient states. -/
noncomputable def mass {s : ℕ} (d : PhaseTypeData s) : ℝ := ∑ i, d.initial i

/-- The generator on the transient states. -/
noncomputable def generator {s : ℕ} (d : PhaseTypeData s) : Matrix (Fin s) (Fin s) ℝ :=
  d.rate • (d.transition - 1)

/-- The discrete Green matrix. Continuous occupation times additionally divide by the rate. -/
noncomputable def green {s : ℕ} (d : PhaseTypeData s) : Matrix (Fin s) (Fin s) ℝ :=
  (1 - d.transition)⁻¹

/-- Absorption at the next event of the uniformizing clock. -/
noncomputable def exit {s : ℕ} (d : PhaseTypeData s) : Fin s → ℝ :=
  (1 - d.transition).mulVec (fun _ ↦ 1)

/-- Probability of absorption at clock event `n + 1`, before adding the zero atom. -/
noncomputable def weight {s : ℕ} (d : PhaseTypeData s) (n : ℕ) : ℝ :=
  dotProduct d.initial ((d.transition ^ n).mulVec d.exit)

end PhaseTypeData
end SSPRK
