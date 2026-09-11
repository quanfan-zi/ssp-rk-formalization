# Third-order proof correspondence

This describes the implementation on `codex/third-order-proof`. The numerical optimum
and optimizer uniqueness in V1.6 Theorem 5.3 are proved. The canonical CTMC path and
occupation constructions are described below and in `formalization-status.md`.

## Moment classes and state elimination

`MomentClass k x a c` records positive parameter and mean, nonnegative second and third
moments, and the two polynomial inequalities

$$
(k+1)x^2\leq ka,\qquad (k+2)a^2\leq(k+1)xc.
$$

`MomentAlgebra.lean` proves closure under independent-sum moment convolution.
`MomentAlgebraEquality.lean` proves the equality implications in Lemma 4.3.
`MomentMixture.lean` and `MomentCountableMixture.lean` prove mixture closure and equality
conditions. Countable mixtures explicitly assume the necessary summability; an unqualified
real-valued infinite sum would not express a probability mass condition in Lean.

For a transient substochastic matrix $P$, let $G=(I-P)^{-1}$ and eliminate state $0$:

$$
R_{ij}=P_{ij}+\frac{P_{i0}P_{0j}}{1-P_{00}},\qquad
\beta_j=\frac{P_{0j}}{1-P_{00}}\quad(i,j\ne0).
$$

`PhaseTypeElimination.lean` proves $1-P_{00}>0$, all reduced PH representation
conditions, $(I-R)^{-1}=G_{bb}$, and $\beta G_{bb}=G_{0b}$. This is valid with cycles.
`PhaseTypePrincipal.lean` proves that
$G_{bb}-G_{b0}G_{0b}/G_{00}$ is the nonnegative Green matrix of the killed principal block.

Normalize time so that the continuous Green matrix has the block form

$$
\widetilde G=\begin{pmatrix}1&u\\v&W\end{pmatrix},\qquad H=W-vu\geq0.
$$

Put $z_1=u\mathbf1$, $z_2=2uW\mathbf1$, $z_3=6uW^2\mathbf1$,
$\eta_1=uv$ and $\eta_2=2uHv$. `PhaseTypeBlockMoments.lean` proves exactly

$$
m_1=z_1+1,\qquad m_2=z_2+2z_1+2(1+\eta_1),
$$

$$
m_3=z_3+3z_2+6z_1(1+\eta_1)+6(1+\eta_1)^2+3\eta_2.
$$

The correction triple $(1,2(1+\eta_1),6(1+\eta_1)^2+3\eta_2)$ belongs to $C_1$.
`PhaseTypeThirdMoment.lean` applies the smaller-state induction and sum closure, handles
$z_1=0$ separately, then restores arbitrary initial rows by mixing. Positive scaling and
the previously proved PH integral formulas yield Theorem 4.1 for actual probability laws.
`PhaseTypeDimensionBounds.lean` also packages the version with at most $s$ states.

## Actual independent replacement and equality

`AuxiliaryScale.lean` constructs the two-point nonnegative scale in Lemma 4.5.
`PhaseTypeReturn.lean` proves the required implication $\eta_1=0\Rightarrow\eta_2=0$.
`ScaledExponential.lean` and `AuxiliaryLaw.lean` turn the scale into an actual mixture
of scaled exponential probability measures, with all natural powers integrable.

`MomentConvolution.lean` constructs independent sums using the pushforward of a product
measure under addition, proves coordinate independence, and derives the first three
integral formulas. `PhaseTypeTimeChange.lean` identifies the normalized original and
reduced moments. The theorem `SSPRK.PhaseTypeData.normalized_independent_replacement`
proves that the resulting
independent convolution has the same first three integrable moments as the original law.
This establishes a replacement distribution. It does not assert independence of actual
occupation times or equality of the replacement's entire law with the original law.

At third-moment equality, `PhaseTypeThirdEquality.lean` forces each supported fixed-start
law to attain the variance bound. `PhaseTypeThirdMixtureEquality.lean` retains the initial
mass factor when mixing. `PhaseTypeThirdLaw.lean` and `PhaseTypeConditioning.lean` prove
the full Corollary 4.6 equivalence: conditional on being positive, the law is equal-rate
Erlang with $s$ phases. An initial zero atom is allowed.

## RK optimum and uniqueness

The feasible RK representation has actual integral moments

$$
m_1=r,\qquad m_2=r^2+2r,\qquad m_3=r^3+6r^2+6r.
$$

The third-moment bound gives $r^2-2(s-1)r-2(s-1)\leq0$ and thus
$r\leq\rho_s=s-1+\sqrt{s^2-1}$. `ThirdOrder.lean` extends this to the full supremum radius.
`SDIRKOrder.lean` verifies all four classical order-three conditions, including
$b^Tc^{\circ2}=1/3$. `SDIRKAttainment.lean` proves feasibility at $\rho_s$ using
$I+\rho_sA=dL$ and inverse $d^{-1}D$. `ThirdOrderOptimality.lean` proves the numerical optimum.

`ThirdOrderUniqueness.lean` applies endpoint feasibility, equality classification and the
inverse RK transform. Every optimizer is the stated SDIRK tableau up to a simultaneous
permutation of stages. This proof obtains representation rigidity from variance equality.
The manuscript's separate Lemma 4.7 route is also proved in `PhaseTypeErlangRigidity.lean`.
Pole counting forces the minimal dimension and characteristic polynomial; the shifted
generator is nonnegative and nilpotent. Uniformization at the Erlang rate gives a
deterministic absorption count. A positive maximal path orders all states, and equality
in the expected visit count excludes skipped states and early absorption. The resulting
generator and initial distribution are the Erlang chain up to permutation. This proof
does not use variance or third-moment equality rigidity.

`PhaseTypeAbsorptionLaw.lean` independently identifies the actual canonical CTMC
jump-record absorption time with the constructed PH measure. The proof establishes
almost-sure absorption from embedded-chain survival probabilities, preserves expectations
of bounded Laplace harmonic observables at every finite record index, and passes to the
terminal value by dominated convergence. Laplace uniqueness then identifies the full law
and transfers all integer moment formulas to the actual absorption-time random variable.

`PhaseTypePath.lean` reads a jointly measurable continuous-time path from these records,
proves the initial law and holding-interval values, and identifies absorption as the first
physical time at zero. `PhaseTypePathOccupation.lean` proves that the record occupation
sums equal stopped path-state indicator integrals. `PhaseTypeOccupationLaw.lean` proves
Lemma 4.4 for that actual occupation variable: omitting the first transient state's time
gives the reduced Schur-complement PH law. Its proof uses a state-dependent reward clock
and bounded one-step harmonic function, followed by dominated convergence and Laplace uniqueness.

The variance theorem uses the finite Green/energy proof described in `second-order-proof.md`;
the manuscript's continuous-time martingale/optional-stopping proof is not separately formalized.
The CTMC core and canonical record law are now extracted into local modules on the
separate `codex/ripple-extraction` branch. See [the extraction inventory](ripple-extraction.md)
for provenance, the dependency boundary, and validation.
