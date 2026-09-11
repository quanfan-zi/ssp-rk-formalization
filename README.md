# ssp-rk-formalization

Lean formalization of SSP-RK theory

This project is used for the Lean formal verification of the SSP-RK theory. Based on the main proof line of the paper V1.6, the repository mainly maintains Lean code.

## Second-order optimality and PH moments

The general second-order bound `r ≤ 2 * s` is proved in
`SSPRK.second_order_rk_ssp_bound` in [SecondOrder.lean](lean/SSPRK/SecondOrder.lean).
Its original statement is unchanged: arbitrary real dense tableaux are allowed, with no
triangularity or acyclicity assumption. The complete supremum radius is also bounded by
`2 * s` in `SSPRK.second_order_radius_bound`. The repeated midpoint family attains
this bound, and `SSPRK.second_order_optimal_radius` proves that the optimal radius
over all second-order tableaux with $s>0$ stages is exactly $2s$.
`SSPRK.second_order_unique_of_radius_eq` proves that every attaining tableau is this
midpoint family up to a simultaneous permutation of stages.

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
[the source correspondence and remaining work](docs/formalization-status.md).

Validated with Lean 4.30.0: `lake build` succeeds, project Lean sources contain no proof
placeholders, and the checked main theorems use only `propext`, `Classical.choice`, and
`Quot.sound`. No custom probability axiom is assumed.

Third-order optimality remains open. Variance equality now determines the full equal-rate
chain representation and its single initial state. The PH measure is proved independent of
the chosen uniformization rate. Matrix-exponential survival/density formulas and identification
with a CTMC path law remain to be proved.

## Build

Run from `lean/`:

```sh
lake build
```

## Project structure

- `docs/V1.6.pdf`: reference manuscript.
- `lean/SSPRK/SecondOrder.lean`: the general second-order SSP upper bound.
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
- `lean/SSPRK/MomentAlgebra.lean`: independent-sum moment inequalities for later work.
- `lean/Main.lean`: imports the modules checked by the default build.
- `lean/lean-toolchain` and `lean/lake-manifest.json`: pinned environment.
