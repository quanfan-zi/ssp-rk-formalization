/-
Derived from pcbcos/Ripple contributors.
Upstream source: Ripple/CTMC/DTMC.lean
Upstream commit: 83d6a77319d1bbb9bd397f9613244d396dc48583
License: Apache-2.0; see repository-root licenses/Ripple-Apache-2.0.txt.
Modifications: retained the DTMC structure and step iteration required by this project.
-/

/-
  Ripple.CTMC.DTMC — Discrete-Time Markov Chains (Countable State Space)

  A DTMC on a countable state space S is specified by a transition kernel
  K : S → PMF S (each row is a probability mass function).

  Uses Mathlib's PMF infrastructure throughout.
-/

import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.ENNReal.Operations

namespace Ripple.CTMC

open PMF
open scoped ENNReal

/-- A discrete-time Markov chain on a countable state space S,
specified by a transition kernel K : S → PMF S. -/
structure DTMC (S : Type*) [Countable S] where
  step : S → PMF S

variable {S : Type*} [Countable S]

/-- The n-step transition kernel K^n, defined by iterated bind. -/
noncomputable def DTMC.stepN (mc : DTMC S) : ℕ → S → PMF S
  | 0 => PMF.pure
  | n + 1 => fun s => (mc.stepN n s).bind mc.step

end Ripple.CTMC
