# V1.6 formalization

The second-order numerical optimum is proved: the general second-order upper bound
`SSPRK.second_order_rk_ssp_bound`, with its original statement unchanged and no `sorry`
in its dependencies, extends to the complete radius; the repeated midpoint family attains
$2s$, and `SSPRK.second_order_optimal_radius` proves the optimum over all second-order
tableaux. `SSPRK.second_order_unique_of_radius_eq` proves full optimizer uniqueness
up to a simultaneous permutation of stages.

The PH construction now defines actual probability measures, proves all integer integral
moments and the minimum-variance inequality, and connects the laws to feasible RK tableaux.
The third-order numerical optimum $s-1+\sqrt{s^2-1}$ is now proved for $s\geq2$,
including the general complete-radius bound, the attaining SDIRK family and uniqueness up
to simultaneous stage permutation. The independent spectral/path proof of Lemma 4.7
is also complete. Actual canonical CTMC jump-record absorption and its full PH law are proved.
The continuous-time path has the prescribed initial law and absorption time. Its occupation
integrals satisfy the same-path decomposition and the deleted-state PH law.
The variance theorem retains the finite Green/energy proof; the continuous-time
martingale/optional-stopping proof is not separately formalized.
The source remains `docs/V1.6.pdf`.

## Source correspondence

| Source | Lean module | Status |
| --- | --- | --- |
| Section 2.4, equations (2.17)-(2.19) | `SSPRK/RKTransform.lean`, `SSPRK/Substochastic.lean` | Transform algebra and convergent Neumann series proved |
| Section 2.6, equations (2.26), (2.28) | `SSPRK/RKTransform.lean` | First three weighted matrix moments proved |
| Theorem 3.1, minimum-variance inequality | `SSPRK/VariancePotential.lean`, `SSPRK/PhaseVariance.lean`, `SSPRK/PhaseMomentBound.lean`, `SSPRK/PhaseTypeVariance.lean` | Finite-state energy bound and actual PH integral/variance inequality proved; equality is listed under Corollary 3.2 |
| Theorem 5.2, bound at every feasible positive radius | `SSPRK/SecondOrder.lean` | Proved with the original statement unchanged |
| Theorem 5.2, complete supremum radius upper bound | `SSPRK/Radius.lean` | Proved; the extended nonnegative real radius also represents infinite radii for general tableaux |
| Equation (5.1), midpoint family | `SSPRK/MidpointOrder.lean`, `SSPRK/ChainMatrices.lean`, `SSPRK/MidpointAttainment.lean` | Order conditions, inverse certificate, feasibility at $2s$, and exact radius proved |
| Lemma 4.2, mixtures | `SSPRK/MomentMixture.lean`, `SSPRK/MomentCountableMixture.lean`, `SSPRK/ProbabilityMomentMixture.lean`, `SSPRK/LengthBiasMixture.lean` | Finite/countable moment bounds and equality conditions proved for actual probability mixtures, including the full length-biased mixture law identity and normalized weights |
| Section 4.1, length bias | `SSPRK/LengthBias.lean` | Actual probability measure, integral change of measure, moments and normalized variance identity proved |
| Lemma 4.3, independent sums | `SSPRK/MomentAlgebra.lean`, `SSPRK/MomentAlgebraEquality.lean`, `SSPRK/MomentConvolution.lean`, `SSPRK/LengthBiasConvolution.lean` | Moment bounds and equality implications, actual independent-sum law and integral closure, and the full length-bias convolution identity proved |
| Proposition 2.2, PH laws and moment formulas | `SSPRK/PhaseType.lean`, `SSPRK/PhaseTypeUniformization.lean`, `SSPRK/PhaseTypeAllMoments.lean`, `SSPRK/PhaseTypeGeneratorMoments.lean`, `SSPRK/PhaseTypeLaplaceGenerator.lean`, `SSPRK/PhaseTypeLaw.lean`, `SSPRK/PhaseTypeDensity.lean`, `SSPRK/PhaseTypeSurvival.lean`, `SSPRK/PhaseTypeAbsorptionLaw.lean` | Probability law, all positive integer moments, Laplace formula, clock invariance, density/survival/CDF and actual canonical absorption-time law proved |
| PH interpretation of the RK transform | `SSPRK/RKPhaseType.lean`, `SSPRK/RKThirdMoment.lean` | Constructed law has generator $-M$ and the first three prescribed integral moments under the respective chain order conditions |
| Corollary 3.2, equality classification | `SSPRK/PhaseMixtureChain.lean`, `SSPRK/PhaseTypeEquality.lean`, `SSPRK/PhaseTypeLawEquality.lean` | Full representation rigidity and the actual variance-equality iff Erlang-law characterization proved |
| Lemma 4.4, state elimination | `SSPRK/PhaseTypeElimination.lean`, `SSPRK/PhaseTypePathOccupation.lean`, `SSPRK/PhaseTypeOccupationLaw.lean` | Reduced PH data, transience, Green identities and the full law of the actual complementary path occupation proved |
| Theorem 4.1, third-moment bound | `SSPRK/PhaseTypeThirdMoment.lean`, `SSPRK/PhaseTypeThirdMomentIntegral.lean` | State-count induction for arbitrary cyclic matrices and actual PH integral inequality proved, with random starts and zero atoms |
| Lemma 4.5, auxiliary replacement | `SSPRK/AuxiliaryScale.lean`, `SSPRK/ScaledExponential.lean`, `SSPRK/AuxiliaryLaw.lean`, `SSPRK/PhaseTypeAuxiliary.lean` | Actual auxiliary probability law, its moment class, and an independent convolution matching all three integrable moments of the normalized PH law proved |
| Corollary 4.6, third-moment equality | `SSPRK/PhaseTypeThirdEquality.lean`, `SSPRK/PhaseTypeThirdMixtureEquality.lean`, `SSPRK/PhaseTypeThirdLaw.lean`, `SSPRK/PhaseTypeConditioning.lean` | Full representation classification and the actual conditional-Erlang-law iff proved |
| Lemma 4.7, minimal Erlang rigidity | `SSPRK/PhaseTypeErlangCharpoly.lean`, `SSPRK/PhaseTypeErlangNilpotent.lean`, `SSPRK/ErlangUniformizedWeights.lean`, `SSPRK/NilpotentLongPath.lean`, `SSPRK/OrderedPhaseChain.lean`, `SSPRK/PhaseTypeErlangRigidity.lean` | Complete independent pole/spectral/path proof, including exact dimension and generator/initial-distribution rigidity; no variance-equality argument used |
| Lemma 5.1, endpoint feasibility | `SSPRK/Endpoint.lean` | Feasible radii form a closed set; every positive finite supremum is feasible |
| Theorem 5.2, attainment and numerical optimum | `SSPRK/MidpointAttainment.lean`, `SSPRK/SecondOrderOptimality.lean` | Proved for every positive stage count |
| Theorem 5.2, uniqueness | `SSPRK/PhaseMixtureChain.lean`, `SSPRK/SecondOrderUniqueness.lean` | Complete midpoint tableau classification up to simultaneous stage permutation proved |
| Theorem 5.3, third-order numerical optimality | `SSPRK/ThirdOrder.lean`, `SSPRK/SDIRKOrder.lean`, `SSPRK/SDIRKAttainment.lean`, `SSPRK/ThirdOrderOptimality.lean` | General complete-radius bound, all four order conditions, SDIRK attainment and numerical optimum proved |
| Theorem 5.3, uniqueness | `SSPRK/ThirdOrderUniqueness.lean` | Full SDIRK tableau classification up to simultaneous stage permutation proved |
| Appendix A, downward closure | `SSPRK/ScaledResolvent.lean`, `SSPRK/DownwardClosure.lean`, `SSPRK/FeasibilityAtZero.lean` | All complete SSP conditions preserved for $0\leq\theta\leq r$; positive feasibility also forces nonnegative tableau coefficients |

## Second-order proof route

For a feasible tableau, put $N=I+rA$, $P=I-N^{-1}$ and $\omega=rb^TN^{-1}$.
The SSP hypotheses imply that $P$ is substochastic. Nonsingularity implies
$N=\sum_{k\geq0}P^k\geq0$.

The finite-state minimum-variance argument is expressed using $m=N\mathbf1$
and a potential $f$ satisfying

$$
m_i^2\leq s f_i,\qquad f_i\leq m_i^2,\qquad
f_i-f_j\leq(m_i-m_j)^2.
$$

The energy identity and multiplication by the nonnegative Green matrix give the
same matrix moment inequality used in Theorem 3.1. This preserves arbitrary cyclic
and dense tableaux. It avoids constructing continuous-time sample paths for the
first milestone; no probability theorem is introduced as an axiom. The PH measure
construction below now supplies the corresponding integral interpretation.

## PH construction and moment formulas

`PhaseTypeData s` contains a substochastic matrix $P$, nonsingular $I-P$, a nonnegative
initial row $\alpha$ of mass at most one, and a positive rate $\nu$. Put
$T=\nu(P-I)$, $G=(I-P)^{-1}$, and

$$
w_n=\alpha P^n(I-P)\mathbf1.
$$

`PhaseTypeWeights.lean` proves $w_n\geq0$ and $\sum_nw_n=\alpha\mathbf1$.
`PhaseType.lean` then defines the probability measure

$$
\mu=(1-\alpha\mathbf1)\delta_0+
\sum_{n\geq0}w_n\operatorname{Gamma}(n+1,\nu),
$$

with the second Gamma parameter interpreted as the rate. Its support is nonnegative and
its atom at zero has mass $1-\alpha\mathbf1$. Uniformization constructs such a representation
from every finite nonsingular subgenerator with nonnegative off-diagonal entries and
nonpositive row sums, using a proved explicit admissible rate.

The binomial Neumann-series identity in `PhaseTypeHigherCountMoments.lean` yields all
factorial counting moments. `ErlangMoments.lean` derives component moments from the gamma
density. Summability of these nonnegative moments justifies integration through the countable
mixture, proving for every $k\geq1$ that

$$
\int x^k\,d\mu(x)=\frac{k!}{\nu^k}\alpha G^k\mathbf1
=k!\alpha(-T)^{-k}\mathbf1.
$$

All natural powers are integrable. The zeroth moment of the complete law is $1$;
the positive-time mixture alone has zeroth moment $\alpha\mathbf1$.
`PhaseTypeVariance.lean` proves $\operatorname{Var}_\mu(x)\geq
(\int x\,d\mu)^2/s$ for $s>0$. `RKPhaseType.lean` connects this inequality to the
original second-order SSP bound using a probability measure with the required moments.

The law is defined through uniformization. `PhaseTypeDensity.lean` proves the matrix-exponential
density $\alpha e^{tT}(-T\mathbf1)$ on nonnegative times. `PhaseTypeSurvival.lean` proves
$\mu((t,\infty))=\alpha e^{tT}\mathbf1$ for $t\geq0$. `PhaseTypeAbsorptionLaw.lean`
identifies this measure with the absorption time of the actual canonical jump-record
process and transfers all generator-inverse moments to that random variable.
`PhaseTypeLaw.lean` proves that any two admissible uniformization
rates give exactly the same measure. `PhaseTypeReindex.lean` proves invariance under
simultaneous relabeling of transient states.

`ErlangLaplace.lean`, `PhaseTypeGeneratingFunction.lean`, `PhaseTypeLaplace.lean`, and
`PhaseTypeLaplaceGenerator.lean` prove the actual Laplace integral for every $u\geq0$:

$$
\int e^{-ux}\,d\mu(x)=1-\alpha\mathbf1+
\alpha(uI-T)^{-1}(-T\mathbf1).
$$

`LaplaceUniqueness.lean` proves that equal Laplace transforms determine finite measures
supported on the nonnegative half-line. Its proof uses a positive exponential tilt,
analytic continuation of the complex moment-generating function, characteristic-function
uniqueness, and removal of the tilt. No probability uniqueness theorem is postulated.

The equality proof is also finite dimensional. `VariancePotentialEquality.lean` makes the
state-count equality force a permutation of equally spaced positive mean levels.
`PhaseVarianceEquality.lean` expresses the energy loss as a sum of nonnegative absorption
and jump deficits. `VariancePotentialLevels.lean` identifies the potential on these levels,
and `PhaseChainEquality.lean` proves every state is reached and every row has the chain form.
`PhaseMixtureChain.lean` forces a single initial top state for a sharp mixture.
`SecondOrderUniqueness.lean` then applies the inverse RK transform and endpoint feasibility.

## Ripple dependency audit

The current workspace pins Ripple to `83d6a77319d1bbb9bd397f9613244d396dc48583`
and mathlib to `c5ea00351c28e24afc9f0f84379aa41082b1188f`, with Lean 4.30.0.
Ripple provides `QMatrix`, exponential holding-time laws and their first two moments,
and canonical path laws. The inspected version does not provide the phase-type
minimum-variance theorem, Erlang classification or a complete PH absorption-time API.
The first milestone therefore proves the required finite matrix inequality directly;
the PH probability construction uses mathlib gamma measures and countable measure sums.
The numerical bounds and PH measure construction use mathlib directly.
`PhaseTypeQMatrix.lean` now constructs Ripple's finite `QMatrix` with an absorbing state,
the prescribed transient generator and absorption rates, and the initial probability law.
`PhaseTypeCanonicalRecords.lean` constructs the initial mixture of actual canonical record
laws. `CanonicalStateMarginals.lean` and `PhaseTypeAbsorptionProper.lean` prove that the
embedded chain governs the state marginals and reaches absorption almost surely.
`PhaseTypeRecordHarmonic.lean`, `PhaseTypeAbsorptionLimit.lean` and
`PhaseTypeAbsorptionLaw.lean` prove the absorption-time law through finite-record conditional
integrals, dominated convergence and Laplace uniqueness. `PhaseTypePath.lean` supplies
the continuous-time path and its first-absorption semantics. `PhaseTypePathOccupation.lean`
and `PhaseTypeOccupationLaw.lean` identify the stopped path integrals and deleted-state law.
The variance proof remains the finite Green/energy argument explained above.
After completing the manuscript formalization, the final dependency audit will extract any
Ripple results actually used into local modules and remove the Ripple package dependency.
The package is still pinned at this stage; dependency removal has not yet been performed.

## Verification on 2026-09-11

- The latest completed integrated `lake build` from `lean/` succeeded (3656 jobs),
  through third-order uniqueness, conditional-Erlang characterization, independent
  three-moment replacement, length-bias law identities, matrix-exponential density/survival,
  the full independent spectral/path Erlang rigidity theorem, exponential clock sums,
  actual canonical absorption properness/law, all absorption-time moment formulas,
  continuous-time path semantics, occupation path integrals and deleted-state law.
- Integrated modules have clean LSP diagnostics. New equality and coupling modules are
  checked separately while in progress and added to the default target when ready.
- `lean_verify` reports exactly `propext`, `Classical.choice`, and `Quot.sound` for
  `SSPRK.second_order_rk_ssp_bound` and `SSPRK.second_order_radius_bound`, with no source warnings.
- The new numerical optimum, PH moment formula, RK probability bridge, endpoint and downward
  closure theorems were checked for standard axioms. PH counting, measure and gamma-moment
  components also passed their targeted builds. No custom axioms or native decision shortcuts
  are introduced.
- Full second-order uniqueness, the fixed-state and mixed-state chain classifications, and
  Laplace uniqueness passed their Lean checks with only the same three standard axioms.
- The third-order supremum bound, numerical optimum and actual auxiliary probability-law
  existence theorem also passed axiom checks with only the same three standard axioms.
- The canonical absorption-law identity and its generator-inverse moment theorem passed
  axiom checks with only the same standard axioms. Ripple's `CanonicalLaw.lean` replays
  two existing style warnings about `maxHeartbeats` comments; project modules are clean.
- The continuous-time first-absorption theorem, occupation integral identities, and actual
  complementary-occupation law were checked with only the same standard axioms.
- Independent source review checked the original theorem signature, cyclic matrices, the
  single-stage case, subprobability weights, and the supremum definition.
- See `second-order-proof.md` for the mathematical correspondence and the finite-matrix
  replacement of the continuous-time martingale argument.
