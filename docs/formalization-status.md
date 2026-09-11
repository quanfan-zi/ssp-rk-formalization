# V1.6 formalization

The second-order numerical optimum is proved: the general second-order upper bound
`SSPRK.second_order_rk_ssp_bound`, with its original statement unchanged and no `sorry`
in its dependencies, extends to the complete radius; the repeated midpoint family attains
$2s$, and `SSPRK.second_order_optimal_radius` proves the optimum over all second-order
tableaux. `SSPRK.second_order_unique_of_radius_eq` proves full optimizer uniqueness
up to a simultaneous permutation of stages.

The PH construction now defines actual probability measures, proves all integer integral
moments and the minimum-variance inequality, and connects the laws to feasible RK tableaux.
The longer-term source remains `docs/V1.6.pdf`.

## Source correspondence

| Source | Lean module | Status |
| --- | --- | --- |
| Section 2.4, equations (2.17)-(2.19) | `SSPRK/RKTransform.lean`, `SSPRK/Substochastic.lean` | Transform algebra and convergent Neumann series proved |
| Section 2.6, equations (2.26), (2.28) | `SSPRK/RKTransform.lean` | First three weighted matrix moments proved |
| Theorem 3.1, minimum-variance inequality | `SSPRK/VariancePotential.lean`, `SSPRK/PhaseVariance.lean`, `SSPRK/PhaseMomentBound.lean`, `SSPRK/PhaseTypeVariance.lean` | Finite-state energy bound and actual PH integral/variance inequality proved; equality classification remains |
| Theorem 5.2, bound at every feasible positive radius | `SSPRK/SecondOrder.lean` | Proved with the original statement unchanged |
| Theorem 5.2, complete supremum radius upper bound | `SSPRK/Radius.lean` | Proved; the extended nonnegative real radius also represents infinite radii for general tableaux |
| Equation (5.1), midpoint family | `SSPRK/MidpointOrder.lean`, `SSPRK/ChainMatrices.lean`, `SSPRK/MidpointAttainment.lean` | Order conditions, inverse certificate, feasibility at $2s$, and exact radius proved |
| Lemma 4.3, independent sums | `SSPRK/MomentAlgebra.lean` | Algebraic moment inequalities proved; probabilistic interpretation and equality case remain |
| Proposition 2.2, PH laws and moment formulas | `SSPRK/PhaseType.lean`, `SSPRK/PhaseTypeUniformization.lean`, `SSPRK/PhaseTypeAllMoments.lean`, `SSPRK/PhaseTypeGeneratorMoments.lean`, `SSPRK/PhaseTypeLaplaceGenerator.lean`, `SSPRK/PhaseTypeLaw.lean` | Probability law, support, zero atom, all positive integer integral moments, resolvent Laplace formula and clock invariance proved; matrix-exponential formulas and CTMC identification remain |
| PH interpretation of the RK transform | `SSPRK/RKPhaseType.lean` | Constructed law has generator $-M$, mean $r$, second moment $r^2+2r$, and variance $2r$ |
| Corollary 3.2, equality classification | `SSPRK/PhaseMixtureChain.lean`, `SSPRK/PhaseTypeEquality.lean`, `SSPRK/ErlangPhaseType.lean`, `SSPRK/ErlangVariance.lean` | Full representation rigidity and standard Erlang law/sharpness proved; the final probability-law iff remains to be packaged |
| Theorem 4.1, Lemmas 4.2, 4.4-4.5, Corollary 4.6 | Not yet formalized | Pending |
| Lemma 4.7, minimal Erlang rigidity | Not yet formalized | Pending |
| Lemma 5.1, endpoint feasibility | `SSPRK/Endpoint.lean` | Feasible radii form a closed set; every positive finite supremum is feasible |
| Theorem 5.2, attainment and numerical optimum | `SSPRK/MidpointAttainment.lean`, `SSPRK/SecondOrderOptimality.lean` | Proved for every positive stage count |
| Theorem 5.2, uniqueness | `SSPRK/PhaseMixtureChain.lean`, `SSPRK/SecondOrderUniqueness.lean` | Complete midpoint tableau classification up to simultaneous stage permutation proved |
| Theorem 5.3, third-order optimality and uniqueness | Not yet formalized | Pending |
| Appendix A, downward closure | `SSPRK/ScaledResolvent.lean`, `SSPRK/DownwardClosure.lean` | All complete SSP conditions preserved for $0<\theta\leq r$ |

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

The law is currently defined through uniformization. Equality with the absorption-time
law of a formal CTMC path process and matrix-exponential survival/density formulas
are not yet proved. `PhaseTypeLaw.lean` proves that any two admissible uniformization
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

## Verification on 2026-09-11

- `lake build` from `lean/` completed successfully (3517 jobs), including all completed
  modules through `Main.lean`.
- Completed modules have clean LSP diagnostics and are imported by the default target.
- `lean_verify` reports exactly `propext`, `Classical.choice`, and `Quot.sound` for
  `SSPRK.second_order_rk_ssp_bound` and `SSPRK.second_order_radius_bound`, with no source warnings.
- The new numerical optimum, PH moment formula, RK probability bridge, endpoint and downward
  closure theorems were checked for standard axioms. PH counting, measure and gamma-moment
  components also passed their targeted builds. No custom axioms or native decision shortcuts
  are introduced.
- Full second-order uniqueness, the fixed-state and mixed-state chain classifications, and
  Laplace uniqueness passed their Lean checks with only the same three standard axioms.
- Independent source review checked the original theorem signature, cyclic matrices, the
  single-stage case, subprobability weights, and the supremum definition.
- See `second-order-proof.md` for the mathematical correspondence and the finite-matrix
  replacement of the continuous-time martingale argument.
