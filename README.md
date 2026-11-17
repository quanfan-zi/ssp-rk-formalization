# ssp-rk-formalization

Lean formalization of SSP-RK theory https://arxiv.org/abs/2610.37425

This project formalizes SSP-RK theory in Lean. The current entries cover all propositions
and theorems of the V2.10 manuscript.

## V2.10 paper entries

The formalization follows the [V2.10 manuscript](docs/V2.10.pdf).
Its three propositions and five theorems have explicit entries in `lean/`, all imported
by [Main.lean](lean/Main.lean). The [working note](docs/Note.md) records
statement interpretation, proof reuse, and differences from the manuscript.

| Paper statement | Entry |
| --- | --- |
| Proposition 2.3: transient subintensity criterion | [Proposition_2_3_TransientSubintensity.lean](lean/Proposition_2_3_TransientSubintensity.lean) |
| Proposition 3.1: RK--PH representation | [Proposition_3_1_RKPHRepresentation.lean](lean/Proposition_3_1_RKPHRepresentation.lean) |
| Proposition 3.2: all-order RK--PH moments | [Proposition_3_2_RKPHMoments.lean](lean/Proposition_3_2_RKPHMoments.lean) |
| Theorem 4.1: Aldous--Shepp variance bound | [Theorem_4_1_AldousShepp.lean](lean/Theorem_4_1_AldousShepp.lean) |
| Theorem 4.2: third-moment ratio and equality | [Theorem_4_2_ThirdMomentBound.lean](lean/Theorem_4_2_ThirdMomentBound.lean) |
| Theorem 4.4: acyclic moment ratios of every order | [Theorem_4_4_AcyclicMomentRatio.lean](lean/Theorem_4_4_AcyclicMomentRatio.lean) |
| Theorem 5.1: second-order optimality and uniqueness | [Theorem_5_1_SecondOrderOptimality.lean](lean/Theorem_5_1_SecondOrderOptimality.lean) |
| Theorem 5.2: third-order optimality and uniqueness | [Theorem_5_2_ThirdOrderOptimality.lean](lean/Theorem_5_2_ThirdOrderOptimality.lean) |

All eight entries are proved without `sorry`. The default build, source-coverage check,
and strict axiom audit pass. The note documents proof-route substitutions and their reasons.

## Second- and third-order optimality

The general second-order bound `r ≤ 2 * s` is proved in
`SSPRK.second_order_rk_ssp_bound` in [SecondOrderBound.lean](lean/SSPRK/Proofs/SecondOrderBound.lean).
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
See [the V2.10 proof correspondence and interpretation notes](docs/Note.md).

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

- [docs/V2.10.pdf](docs/V2.10.pdf): current reference manuscript.
- `lean/Proposition_*.lean`, `Theorem_*.lean`: the eight numbered V2.10 entries.
- `lean/SSPRK/Proofs/SecondOrderBound.lean`: the general second-order SSP upper bound.
- `lean/SSPRK/Radius.lean`: the feasible set, extended radius, and its upper bound.
- `lean/SSPRK/Substochastic.lean`: the convergent Neumann series and inverse nonnegativity.
- `lean/SSPRK/RKTransform.lean`, `RKSubstochastic.lean`: the RK transform and matrix moments.
- `lean/SSPRK/VariancePotential.lean`, `PhaseVariance.lean`, `PhaseMomentBound.lean`:
  the finite-state minimum-variance inequality.
- `lean/SSPRK/MidpointAttainment.lean`, `SecondOrderOptimality.lean`: midpoint attainment
  and the optimal second-order radius.
- `lean/SSPRK/Endpoint.lean`, `DownwardClosure.lean`: closed endpoints and smaller radii.
- `lean/SSPRK/SecondOrderRadiusEquality.lean`: full second-order optimizer uniqueness.
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
- `lean/SSPRK/ThirdMomentDefect.lean`, `PhaseTypeThirdDefect.lean`,
  `PhaseTypeThirdDefectEquality.lean`: the defect identity, state-count induction,
  and equality classification for the PH third-moment bound.
- `lean/SSPRK/AcyclicPaths.lean`, `AcyclicMomentBound.lean`: finite path expansion
  and all adjacent moment bounds for acyclic PH laws.
- `lean/SSPRK/ThirdOrderRadius.lean`, `ThirdOrderOptimality.lean`: the general third-order
  complete-radius bound and numerical optimum.
- `lean/SSPRK/ThirdOrderRadiusEquality.lean`: full third-order optimizer uniqueness.
- `lean/SSPRK/SDIRKOrder.lean`, `SDIRKAttainment.lean`: all four order-three conditions
  and the explicit feasible SDIRK family.
- `lean/SSPRK/PhaseTypeDensity.lean`: the matrix-exponential PH density formula.
- `lean/SSPRK/CTMC/`: the local finite CTMC core and canonical record measure.
- `lean/Main.lean`: imports the modules checked by the default build.
- `lean/lean-toolchain` and `lean/lake-manifest.json`: pinned environment.
