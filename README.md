# ssp-rk-formalization

Lean formalization of SSP-RK theory

This project formalizes the sharp second- and third-order SSP-RK bounds and optimizer
classifications of V1.6 in Lean. The [proof correspondence review](ProofCorrespondence.md)
checks the statements and actual proof dependencies, and explains the substantive
substitutions in the formal proofs. Its [review record](docs/proof-correspondence-review.md)
records completed checks and provides a worksheet for external reviewers.

The four public entries state the order conditions and all four SSP inequalities explicitly:

| Conclusion | Entry file |
| --- | --- |
| Second-order upper bound | [SecondOrderBound.lean](lean/SecondOrderBound.lean) |
| Third-order upper bound | [ThirdOrderBound.lean](lean/ThirdOrderBound.lean) |
| Second-order equality classification | [SecondOrderEquality.lean](lean/SecondOrderEquality.lean) |
| Third-order equality classification | [ThirdOrderEquality.lean](lean/ThirdOrderEquality.lean) |

## Second- and third-order optimality

The general second-order bound `r ≤ 2 * s` is proved in
`SSPRK.second_order_rk_ssp_bound` in [SecondOrderBound.lean](lean/SecondOrderBound.lean).
Its original statement is unchanged: arbitrary real dense tableaux are allowed, with no
triangularity or acyclicity assumption. The complete supremum radius is also bounded by
`2 * s` in `SSPRK.second_order_radius_bound`. The repeated midpoint family attains
this bound, and `SSPRK.second_order_optimal_radius` proves that the optimal radius
over all second-order tableaux with $s>0$ stages is exactly $2s$.
`SSPRK.second_order_unique_of_radius_eq` proves that every attaining tableau is this
midpoint family up to a simultaneous permutation of stages.

For $s\geq2$, `SSPRK.third_order_optimal_radius` proves the numerical third-order optimum
$s-1+\sqrt{s^2-1}$. The general upper bound uses the PH third-moment inequality with actual
probability integrals. The SDIRK family satisfies all four classical order-three conditions
and attains this complete radius. `SSPRK.third_order_unique_of_radius_eq` proves that every
attaining tableau is this family up to a simultaneous permutation of stages.

Finite phase-type probability measures are constructed as countable Erlang mixtures with
an optional atom at zero. General finite nonsingular subgenerators admit this construction
by uniformization. All natural powers are proved integrable, and for $k\geq1$ their moments are

$$
\int x^k\,d\mu(x)=k!\,\alpha(-T)^{-k}\mathbf1.
$$

The minimum-variance inequality is proved for these actual measures. Feasible RK tableaux
produce PH laws with mean $r$ and variance $2r$ under the two order conditions.
Endpoint feasibility and downward closure of the complete SSP conditions are also proved.
See [the proof explanation](docs/second-order-proof.md) and
[the third-order proof correspondence](docs/third-order-proof.md), together with
[the source correspondence and remaining work](docs/formalization-status.md).

Validated with Lean 4.30.0: the integrated `lake build` succeeds, integrated modules contain
no proof placeholders, and the checked main theorems use only `propext`, `Classical.choice`, and
`Quot.sound`. No custom probability axiom is assumed.

Variance equality determines the full equal-rate chain representation and its single initial
state, and is equivalent to an Erlang law. The PH measure is proved independent of
the chosen uniformization rate. Matrix-exponential density, survival and CDF formulas
are proved. The actual canonical CTMC jump-record process absorbs almost surely, and
its absorption-time law equals the constructed PH measure; all generator moment formulas
therefore hold for that random variable. A jointly measurable continuous-time path stays
absorbed after its first zero-state time. Its state occupations recover the actual stopped
path integrals, and deleting the first state's occupation gives the Schur-complement PH law.

## Build

Run from `lean/`:

```sh
lake build
```

Mathlib is the only direct external dependency. The CTMC definitions and record-law
lemmas used from Ripple are extracted into `lean/SSPRK/CTMC/`; see the
[dependency inventory and provenance](docs/ripple-extraction.md) and the retained
[Apache-2.0 license](licenses/Ripple-Apache-2.0.txt).

## Project structure

- `docs/V1.6.pdf`: reference manuscript.
- `lean/SecondOrderBound.lean`, `ThirdOrderBound.lean`, `SecondOrderEquality.lean`,
  `ThirdOrderEquality.lean`: the four explicit public entries listed above.
- `lean/SSPRK/Radius.lean`: the feasible set, extended radius, and its upper bound.
- `lean/SSPRK/Substochastic.lean`: the convergent Neumann series and inverse nonnegativity.
- `lean/SSPRK/RKTransform.lean`, `RKSubstochastic.lean`: the RK transform and matrix moments.
- `lean/SSPRK/VariancePotential.lean`, `PhaseVariance.lean`, `PhaseMomentBound.lean`:
  the finite-state minimum-variance inequality.
- `lean/SSPRK/MidpointAttainment.lean`, `SecondOrderOptimality.lean`: midpoint attainment
  and the optimal second-order radius.
- `lean/SSPRK/Endpoint.lean`, `DownwardClosure.lean`: closed endpoints and smaller radii.
- `lean/SSPRK/SecondOrderUniqueness.lean`: full second-order optimizer uniqueness.
- `lean/SSPRK/PhaseMixtureChain.lean`: full chain representation at variance equality.
- `lean/SSPRK/PhaseTypeData.lean`, `PhaseType.lean`, `PhaseTypeUniformization.lean`:
  finite PH representations, probability measures, and general subgenerators.
- `lean/SSPRK/ErlangMoments.lean`, `PhaseTypeHigherCountMoments.lean`,
  `PhaseTypeAllMoments.lean`: all integer moment formulas and integrability.
- `lean/SSPRK/PhaseTypeGeneratorMoments.lean`: the generator-inverse moment formula.
- `lean/SSPRK/PhaseTypeLaplaceGenerator.lean`: the actual PH Laplace integral and
  its generator resolvent formula.
- `lean/SSPRK/LaplaceUniqueness.lean`, `PhaseTypeLaw.lean`, `PhaseTypeReindex.lean`:
  Laplace uniqueness and invariance under clock choice and state permutations.
- `lean/SSPRK/ErlangPhaseType.lean`, `ErlangVariance.lean`: the standard chain's Gamma
  measure and sharp variance formula.
- `lean/SSPRK/PhaseTypeVariance.lean`, `RKPhaseType.lean`: the PH variance bound
  and its probability-law connection to RK tableaux.
- `lean/SSPRK/MomentAlgebra.lean`, `MomentAlgebraEquality.lean`, `MomentMixture.lean`:
  sum and mixture moment inequalities and their equality conditions.
- `lean/SSPRK/PhaseTypeThirdMoment.lean`, `PhaseTypeThirdMomentIntegral.lean`:
  the state-count induction and the actual PH third-moment inequality.
- `lean/SSPRK/ThirdOrder.lean`, `ThirdOrderOptimality.lean`: the general third-order
  complete-radius bound and numerical optimum.
- `lean/SSPRK/ThirdOrderUniqueness.lean`: full third-order optimizer uniqueness.
- `lean/SSPRK/SDIRKOrder.lean`, `SDIRKAttainment.lean`: all four order-three conditions
  and the explicit feasible SDIRK family.
- `lean/SSPRK/AuxiliaryScale.lean`, `ScaledExponential.lean`, `AuxiliaryLaw.lean`:
  a nonnegative probability law realizing the three state-elimination correction moments.
- `lean/SSPRK/PhaseTypeAuxiliary.lean`, `MomentConvolution.lean`: the actual independent
  convolution matching the first three PH integral moments.
- `lean/SSPRK/LengthBias.lean`: the length-biased law and its normalized variance identity.
- `lean/SSPRK/PhaseTypeDensity.lean`: the matrix-exponential PH density formula.
- `lean/SSPRK/CTMC/`: the local finite CTMC core and canonical record measure.
- `lean/scripts/AuditCTMC.lean`: the elaborated constant-dependency and axiom audit.
- `lean/scripts/AuditCorrespondence.lean`, `summarize_correspondence.py`: the actual
  proof-dependency evidence used by `ProofCorrespondence.md`.
- `lean/Main.lean`: imports the modules checked by the default build.
- `lean/lean-toolchain` and `lean/lake-manifest.json`: pinned environment.
