# Paper-to-Lean proof correspondence

This review finds agreement with V1.6 at the level of the RK transform, the sharp
moment inequalities, and recovery of the attaining tableaux. It does **not** find
an identical chain of intermediate theorems. The minimum-variance argument is
replaced by a finite Green-matrix energy proof; the third-moment argument is
implemented as an induction on moment triples; both uniqueness proofs recover
the representation directly from moment equality rather than invoking the
paper's independent minimal-Erlang rigidity lemma. These are substantive,
documented proof substitutions, not just changes of notation.

The reviewed source is commit **`a784414ad1cdb22ae9e868a8e829e80b9b035b23`**, fetched
from `origin/main` on 2026-09-12. The manuscript is [V1.6.pdf][paper], 23 pages,
SHA-256 `9ae32035fae9df6401a6759df4409804b1104a175f3f1fa99e478491e975a0c9`.
All declaration links below point to this fixed source revision. This branch
adds review material and audit tools without changing the mathematical sources.
The [machine evidence](docs/audits/proof-correspondence.json) and
[review record](docs/proof-correspondence-review.md) state what was checked.

## 1. What the four entries say

All entries quantify over arbitrary real matrices $A\in\mathbb R^{s\times s}$
and real weights $b$. They assume neither triangularity nor absence of cycles,
nor entrywise nonnegativity of $A,b$. `Fin s` is the finite stage index set;
matrix/vector order is componentwise. Let $e$ denote the all-ones column and
$\rho_s=s-1+\sqrt{s^2-1}$.

| Entry and fixed-source declaration | Hypotheses beyond $A,b$ | Conclusion and paper scope |
| --- | --- | --- |
| **B2:** [SSPRK.second_order_rk_ssp_bound] | $s\geq1$, $r>0$, invertible $I+rA$, $b^Te=1$, $b^TAe=1/2$, four SSP inequalities below | $r\leq2s$; the positive-feasible-parameter part of Theorem 5.2, pp. 18-19 |
| **B3:** [SSPRK.third_order_rk_ssp_bound] | $s\geq2$, the B2 assumptions, and $b^TA^2e=1/6$ | $r\leq\rho_s$; the corresponding part of Theorem 5.3, pp. 19-20 |
| **E2:** [SSPRK.second_order_unique_at_twice_stages] | $s\geq1$, $r=2s$, the same invertibility, order-two, and SSP assumptions | A simultaneous stage permutation gives exactly (5.1); necessity of the midpoint classification |
| **E3:** [SSPRK.third_order_unique_at_radius] | $s\geq2$, $r=\rho_s$, the same invertibility, three chain conditions, and SSP assumptions | A simultaneous stage permutation gives exactly (5.3)-(5.4); necessity of the SDIRK classification |

The explicit conditions `ham1`-`ham4` are

$$
Me\geq0,\qquad rAM\geq0,\qquad b^TM\geq0,\qquad 1-rb^TMe\geq0,
\quad M=(I+rA)^{-1}.
$$

For $r>0$, these are (2.16): $rAM\geq0$ is equivalent to $AM\geq0$;
$Me\geq0$ is equivalent to $rAMe\leq e$ since $M+rAM=I$.
The determinant hypothesis is essential because Lean's matrix inverse is a total
operation. E2/E3 obtain positivity from their prescribed sharp radius and stage
count. Their conclusion `A.submatrix f f` uses the **same** equivalence $f$ on
rows and columns, with weights $b(f(j))$. The displayed lower-triangular families
therefore have the orientation in (5.1)/(5.4), including diagonal and zero entries.

B3 and E3 omit the bush condition $b^T(Ae)^{\circ2}=1/3$. Their assumptions are
weaker than classical order three, so their conclusions apply to a larger class.
This matches the observation after (2.29). The attaining SDIRK family separately
satisfies the bush condition via [SSPRK.sdirk_order_three_node] and the chain
condition via [SSPRK.sdirk_order_three_tree]. No claim of full order three is
inferred from only the three chain conditions.

The four entries are not, individually, the complete supremum/attainment theorems.
[SSPRK.absoluteMonotonicityRadius] takes the extended nonnegative supremum of
$\{0\}\cup\{r>0:(K)_r\}$, also allowing $+\infty$ before an upper bound is proved.
[SSPRK.second_order_radius_bound] and [SSPRK.third_order_radius_bound] pass from
positive feasible parameters to that supremum. [SSPRK.midpoint_radius] and
[SSPRK.sdirk_radius] prove attainment; [SSPRK.second_order_optimal_radius] and
[SSPRK.third_order_optimal_radius] take the supremum over the tableaux satisfying
the respective order conditions. The third-order set includes **all four** conditions.
[SSPRK.second_order_unique_of_radius_eq] and [SSPRK.third_order_unique_of_radius_eq]
use [SSPRK.absolutelyMonotoneAt_absoluteMonotonicityRadius] (Lemma 5.1) before
applying the internal classifications. E2/E3 already assume endpoint feasibility
and therefore do not themselves call that endpoint theorem.

Here “order” and “SSP radius” refer to the paper's algebraic tableau conditions.
The project does not separately formalize the standard equivalence with ODE
convergence order or the nonlinear stability interpretation of absolute monotonicity.

## 2. The normalization dictionary

Section 2.4 uses $N=I+rA$, $M=N^{-1}$, $P=I-M$, $\omega^T=rb^TM$,
$\sigma=\omega^Te$, and the normalized initial row $\pi=\omega^T/\sigma$.
The code's `rkN`, `rkM`, `rkP`, `rkOmega`, and `rkSigma` have these meanings.
[SSPRK.AbsolutelyMonotoneAt.phaseType] uses rate $1$, transition $P$, initial row
$\alpha=\omega^T$, generator $T=P-I=-M$, and Green matrix $N$.

Its measure is the paper's **output time** $\tau^\circ$, including the atom
$1-\sigma$ at zero. It is not silently identified with the positive conditional
time $\tau\sim\mathrm{PH}(\pi,T)$. For positive feasible $r$, consistency forces
$\sigma>0$ because $\omega^TNe=r>0$, while SSP gives $\sigma\leq1$.

| Quantity | Positive conditional time $\tau$ | Code's output law $\tau^\circ$ |
| --- | --- | --- |
| First moment | $r/\sigma$ | $r$ |
| Second moment | $(r^2+2r)/\sigma$ | $r^2+2r$ |
| Third moment, with the chain condition | $(r^3+6r^2+6r)/\sigma$ | $r^3+6r^2+6r$ |
| $H_1$ | $\sigma(1+2/r)$ | $1+2/r$ |
| $H_2$ | $(r^2+6r+6)/(r+2)^2$ | The same ratio |

The conversion is proved for every positive integer moment by
[SSPRK.PhaseTypeData.normalizeInitial_integral_pow]. The actual conditional-law
identity is [SSPRK.PhaseTypeData.cond_positive_eq_normalizeInitial]. These are
supporting interpretation results, not calls made by all four entries.
The general PH moment theorems allow arbitrary positive clock rate; the integral
conversion divides the $k$th Green moment by that rate to the power $k$.

The moment bounds use the actual dimension. The manuscript's “at most $s$”
versions are supplied by [SSPRK.PhaseTypeData.variance_lower_bound_of_le] and
[SSPRK.PhaseTypeData.third_moment_lower_bound_of_le]. A zero-state representation
cannot satisfy the positive-mean hypothesis; a pure zero atom is likewise excluded.
Second-order statements include $s=1$; the third-order RK statements start at $s=2$.

## 3. The four actual proof routes

The tables below group low-level proof steps into mathematical nodes. Each listed
core declaration is reachable from its indicated entry in the elaborated proof
graph. “Translation” means a change of representation or algebraic formulation;
“replacement” means a different argument supplies the required conclusion.

### B2: the second-order bound

| Paper node | Actual Lean node and its role | Correspondence |
| --- | --- | --- |
| (2.17)-(2.19), p. 7 | [SSPRK.rkP_substochastic], [SSPRK.rkN_nonneg]: produce a transient substochastic transform and nonnegative inverse | Translation; transience/Neumann-series facts apply to cyclic matrices |
| Theorem 3.1, pp. 10-11 | [SSPRK.phase_second_moment_bound], through [SSPRK.exists_variance_potential] and [SSPRK.phase_variance_pointwise_of_potential] | Replacement of the martingale/optional-stopping derivation by finite energy inequalities |
| (2.26), p. 9 | [SSPRK.rkOmega_N_ones_eq], [SSPRK.rkOmega_N_sq_ones_eq] | Direct evaluation of the two weighted matrix moments |
| Theorem 5.2, p. 18 | [SSPRK.second_order_bound_of_weighted_moment_inequality] | Scalar conclusion $r\leq2s$ |

The finite energy argument is recognizably related to the paper's lifetime-gap
mechanism. Write $m=Ne$ and $a=(I-P)e$. Its energy vector is

$$
q_i=a_i m_i^2+\sum_jP_{ij}(m_i-m_j)^2,
\qquad Nq=2Nm-m^{\circ2}.
$$

The constructed potential satisfies $m_i^2\leq s f_i$, $f_i\leq m_i^2$, and
$f_i-f_j\leq(m_i-m_j)^2$. Consequently $(I-P)f\leq q$ and, since $N\geq0$,
$m_i^2/s\leq f_i\leq(Nq)_i$. The code establishes this through matrix identities
and finite sums. The paper obtains the expected jump energy using a remaining-life
martingale stopped at $\tau\wedge n$, then bounds it by successive lifetime gaps.
That stochastic derivation, including its stopping-time limit, is not formalized.

The final subprobability inequality is $(s+1)(\omega^TNe)^2\leq2s\omega^TN^2e$.
Substitution yields $(s+1)r^2\leq s(r^2+2r)$ and hence $r\leq2s$.
This applies Theorem 3.1's zero-atom version directly to $\tau^\circ$; it does not
retain the paper's stronger intermediate conditional estimate
$1+1/s\leq\sigma(1+2/r)$. Both routes give the same required RK bound.

### B3: the third-order bound

| Paper node | Actual Lean node and its role | Correspondence |
| --- | --- | --- |
| (2.25)-(2.29), pp. 9, 19 | [SSPRK.AbsolutelyMonotoneAt.phaseType], [SSPRK.PhaseTypeData.third_moment_lower_bound], the two moment identities in B2, and [SSPRK.rkOmega_N_cu_ones_eq] | Actual PH integral moments; $\sigma$ cancels from $H_2$ |
| State-count induction, p. 16 | [SSPRK.PhaseTypeData.green_moment_class], [SSPRK.PhaseTypeData.green_zero_momentClass_of_induction] | Same induction on a fixed start, then mixtures; proves both moment inequalities simultaneously |
| Lemma 4.4 and normalization, pp. 14-15 | [SSPRK.PhaseTypeData.eliminateZero], [SSPRK.PhaseTypeData.normalizedGreen] | Same Schur-complement smaller PH representation; actual occupation-law proof is separate |
| (4.16)-(4.18), pp. 15-16 | [SSPRK.phaseBlock_third_moment], [SSPRK.auxiliary_moment_class] | Block identities match the first three moments; no random auxiliary variable is needed by this core proof |
| Lemmas 4.2-4.3, pp. 12-13 | [SSPRK.MomentClass.add], [SSPRK.length_biased_component_bound], [SSPRK.MomentClass.finite_mixture] | Moment algebra implements the length-biased two-component comparison and mixing |
| Theorem 5.3, p. 19 | [SSPRK.third_order_quadratic_of_moment_bound], [SSPRK.third_order_bound_of_quadratic] | The same quadratic and upper-root selection |

Here the induction hypothesis is the full algebraic class

$$
\mathcal C_k:\quad (k+1)m_1^2\leq k m_2,\qquad
(k+2)m_2^2\leq(k+1)m_1m_3,
$$

with positive $k,m_1$ and nonnegative $m_2,m_3$. Thus B3 does **not** call the
standalone minimum-variance theorem to supply the smaller model's first bound,
as the paper does; the strengthened induction hypothesis already contains it.

To check the block correspondence, normalize the Green pivot to one and write
$\bar G=G/G_{00}=\begin{pmatrix}1&u\\v&W\end{pmatrix}$ and $H=W-vu$.
The code uses $\eta_1=uv$, $\eta_2=2uHv$, and
$z_1=ue$, $z_2=2uWe$, $z_3=6uW^2e$.
In the paper's normalized generator blocks, $H=(-B)^{-1}$,
$u=r^T(-B)^{-1}$, $v=(-B)^{-1}q$, so these are exactly (4.15).
The reduced generator is $B+qr^T/\lambda_1$, not just $B$; its Green matrix is $W$.
The normalized `phaseBlock_*_moment` identities are

$$
m_1=z_1+1,\quad m_2=z_2+2z_1+2(1+\eta_1),
$$
$$
m_3=z_3+3z_2+6z_1(1+\eta_1)+6(1+\eta_1)^2+3\eta_2.
$$

These are the independent-sum formulas with auxiliary triple
$(1,2(1+\eta_1),6(1+\eta_1)^2+3\eta_2)$ from (4.17).
`MomentClass.add` actually calls the two length-biased component bounds before
mixing them; it is not an unrelated estimate that merely has the same endpoint.
The zero-tail case is handled separately by the exponential triple $(1,2,6)$;
positive scaling and finite mixtures restore the other starting states and zero mass.

The core proves membership of the auxiliary **triple** directly from
$\eta_1,\eta_2\geq0$. It does not use the two-point random-scale construction,
nor need the extra implication $\eta_1=0\Rightarrow\eta_2=0$ required to realize
that triple by the particular probability law. The actual existence and independent
replacement theorem [SSPRK.PhaseTypeData.normalized_independent_replacement]
is separately proved, with that extra property supplied for these PH data.
This is a mathematical interpretation of the core calculation, not a dependency
of B3. No independence of the actual occupation totals $L,Z$ is asserted.

### E2: second-order equality

| Paper node | Actual Lean node and its role | Correspondence |
| --- | --- | --- |
| Equality in the bound, p. 19 | [SSPRK.second_order_classification_at_bound] substitutes $r=2s$ into the first two weighted moments | Direct equality calculation |
| Corollary 3.2 and representation recovery | [SSPRK.phase_mixture_chain_classification_of_pos], using [SSPRK.phase_variance_chain_classification] | Energy-equality replacement yields the chain representation itself, with mass one and a single top initial state |
| (5.2), p. 19 | [SSPRK.eq_midpoint_of_sorted_transform] | Mean $2s$ fixes the Green scale to $2$; inverse transform recovers (5.1) |

The paper goes from variance equality to an Erlang law, then invokes Lemma 4.7.
Write $L_{ij}=1$ for $j\leq i$ and $0$ otherwise; $e_s$ denotes the last basis
vector in one-based notation. E2 obtains $N=2L$ and $\omega^T=e_s^T$ directly from equality in the
finite energy/mixture proof. The lifetime-level rigidity mechanism of Corollary
3.2 remains visible, but the separate spectral lemma is bypassed. It is therefore
inaccurate to describe this entry as a formal execution of the paper's entire
law-then-representation chain.

### E3: third-order equality

| Paper node | Actual Lean node and its role | Correspondence |
| --- | --- | --- |
| Equality in Theorem 4.1, p. 20 | [SSPRK.third_order_classification_at_bound] substitutes $r=\rho_s$ and the three matrix moments | Direct equality calculation |
| Corollary 4.6, pp. 16-17 | [SSPRK.PhaseTypeData.green_second_eq_of_third_eq], [SSPRK.PhaseTypeData.green_mixture_second_eq_of_third_eq] | Same reduction from sharp third moments to sharp variance for normalized positive starts, expressed algebraically |
| Representation recovery | [SSPRK.PhaseTypeData.third_equality_representation], then [SSPRK.phase_mixture_chain_classification_of_pos] | Direct moment-to-representation classification; bypasses the law-level Corollary 4.6 theorem and Lemma 4.7 as calls |
| (5.2)-(5.4), p. 20 | [SSPRK.eq_sdirk_of_sorted_transform] | Moment ratio fixes $a=(\rho_s+2)/(s+1)=1+(s-1)/\sqrt{s^2-1}$; $N=aL$ recovers SDIRK coefficients |

The initial mass is not forced to one: the first moment gives
$\rho_s=\sigma s a$, hence $\sigma=\sqrt{s^2-1}/s<1$.
The positive conditional law is Erlang with rate $1/a$; the output law has a
nonzero atom at zero. The separate iff theorem
[SSPRK.PhaseTypeData.third_integral_eq_iff_cond_erlang] states this distinction
explicitly. Equality of three arbitrary moments alone is never used to identify
a distribution: the PH equality classification supplies the extra rigidity.

## 4. Actual use versus separately proved interpretation

The following is a reachability result about the **compiled entries**, not imports.
“Yes” includes transitive dependencies; “No” means no path even when dependencies
in both declaration types and values are included.

| Named node | B2 | B3 | E2 | E3 |
| --- | --- | --- | --- | --- |
| `phase_variance_pointwise_of_potential` | Yes | No | Yes | Yes |
| `PhaseTypeData.green_moment_class` | No | Yes | No | Yes |
| `length_biased_component_bound` / `MomentClass.add` | No | Yes | No | Yes |
| `PhaseTypeData.eliminateZero` | No | Yes | No | Yes |
| `phase_mixture_chain_classification_of_pos` | No | No | Yes | Yes |
| [SSPRK.lengthBias_normalized_variance] / [SSPRK.lengthBias_independentSumLaw] / [SSPRK.lengthBias_probabilityMomentMixture] | No | No | No | No |
| [SSPRK.PhaseTypeData.normalized_independent_replacement] | No | No | No | No |
| [SSPRK.PhaseTypeData.canonicalRecords_map_absorptionTime] / [SSPRK.PhaseTypeData.canonicalRecords_map_occupationRest] | No | No | No | No |
| [SSPRK.PhaseTypeData.erlang_rigidity_of_num_phases_le] | No | No | No | No |

All “No” supporting theorems in this table are present in `Main` and pass the
project axiom audit. Their mathematical roles are, respectively, the length-bias
identities (4.3)/(4.8), the actual replacement (4.18), the canonical absorption and
deleted-occupation laws, and independent Lemma 4.7. Existence does not make them
steps in the four entries. Similarly, the general PH law is initially constructed
as an Erlang mixture and later identified with CTMC absorption; the paper starts
from a CTMC and derives its analytic formulas. This reverses the construction order.

The four dependency closures contain 54, 240, 126, and 308 project constants,
respectively, including the entry itself and generated helpers. The saved JSON
includes a witness path, with type/value edge labels, for every positive query;
negative queries are `null`. Source reading is still necessary to interpret the
mathematical role of a dependency. These counts are not measures of proof length.

## 5. How a reviewer can assess the claim

The [Lean reference manual][lean-validation] explicitly separates a valid proof
from the meaning of its statement. A common practice is a human-readable blueprint
with links to Lean declarations: [leanblueprint][blueprint] lists many users,
including the Liquid Tensor Experiment and PFR, and [Tao's PFR tour][pfr] shows the
workflow. Its `\lean` names declarations, `\uses` records author-specified LaTeX
dependencies, and `\leanok` claims formalization status. `checkdecls` checks that
named declarations exist; it is not a mathematical-equivalence or route checker.
[ConNF][connf] also provides a proof following the code and a deformalisation paper,
while explicitly warning that intended English meanings require careful checking.
These sources were checked on 2026-09-12; no Blueprint installation is needed here.

For this project the defensible claim is: **the formalization preserves the RK
reduction and the state-elimination/moment-comparison strategy, with explicit
Green-energy and equality-classification substitutions.** An unqualified claim
that all four proofs follow the manuscript's exact intermediate dependency chains
would be false. A reviewer who requires the actual martingale proof or mandatory
use of Lemma 4.7 should treat that as a stricter requirement not met by this version.

From `lean/`, with Lake and Python 3 on `PATH`, reproduce the checks in PowerShell:

```powershell
lake build
lake env lean scripts/AuditProofs.lean
lake env lean scripts/AuditCorrespondence.lean | Set-Content -Encoding utf8 .lake/proof-correspondence-full.json
python scripts/summarize_correspondence.py --revision a784414ad1cdb22ae9e868a8e829e80b9b035b23
```

The last two tools are added by this review branch; the revision argument labels
the independently checked mathematical baseline, not a revision inferred by Python.
The JSON also fingerprints the manuscript and all imported mathematical source
files, with line endings normalized to LF. Rebuild after changing those files.
The pinned environment is Lean 4.30.0 and mathlib commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f` (`lean/lake-manifest.json`).
The completed build had 3,653 jobs; all 1,620 imported project declarations,
including the four entries, use only `propext`, `Classical.choice`, and `Quot.sound`.

For external review, ask a mathematician to verify the statements, normalization
table, and acceptability of each replacement; ask a Lean reviewer to check the
declarations and witness paths against that explanation. Record specific inspected
nodes and unresolved objections using the linked review record. This report is a
model-assisted source/dependency audit, not an external human endorsement. Neither
a green dependency diagram nor kernel checking can replace that semantic judgment.

[paper]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/docs/V1.6.pdf
[lean-validation]: https://lean-lang.org/doc/reference/latest/ValidatingProofs/
[blueprint]: https://github.com/PatrickMassot/leanblueprint#editing-the-blueprint
[pfr]: https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/
[connf]: https://leanprover-community.github.io/con-nf/

<!-- Declaration links are generated from the elaborated source ranges. -->
[SSPRK.AbsolutelyMonotoneAt.phaseType]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/RKPhaseType.lean#L19
[SSPRK.MomentClass.add]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/MomentAlgebra.lean#L91
[SSPRK.MomentClass.finite_mixture]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/MomentMixture.lean#L28
[SSPRK.PhaseTypeData.canonicalRecords_map_absorptionTime]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/PhaseTypeAbsorptionLaw.lean#L41
[SSPRK.PhaseTypeData.canonicalRecords_map_occupationRest]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/PhaseTypeOccupationLaw.lean#L49
[SSPRK.PhaseTypeData.cond_positive_eq_normalizeInitial]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/PhaseTypeConditioning.lean#L44
[SSPRK.PhaseTypeData.eliminateZero]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/PhaseTypeElimination.lean#L121
[SSPRK.PhaseTypeData.erlang_rigidity_of_num_phases_le]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/PhaseTypeErlangRigidity.lean#L123
[SSPRK.PhaseTypeData.green_mixture_second_eq_of_third_eq]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/PhaseTypeThirdMixtureEquality.lean#L104
[SSPRK.PhaseTypeData.green_moment_class]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/PhaseTypeThirdMoment.lean#L216
[SSPRK.PhaseTypeData.green_second_eq_of_third_eq]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/PhaseTypeThirdEquality.lean#L87
[SSPRK.PhaseTypeData.green_zero_momentClass_of_induction]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/PhaseTypeThirdMoment.lean#L178
[SSPRK.PhaseTypeData.normalizeInitial_integral_pow]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/PhaseTypeNormalization.lean#L73
[SSPRK.PhaseTypeData.normalizedGreen]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/PhaseTypeThirdMoment.lean#L60
[SSPRK.PhaseTypeData.normalized_independent_replacement]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/PhaseTypeAuxiliary.lean#L19
[SSPRK.PhaseTypeData.third_equality_representation]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/PhaseTypeThirdLaw.lean#L65
[SSPRK.PhaseTypeData.third_integral_eq_iff_cond_erlang]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/PhaseTypeConditioning.lean#L65
[SSPRK.PhaseTypeData.third_moment_lower_bound]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/PhaseTypeThirdMomentIntegral.lean#L43
[SSPRK.PhaseTypeData.third_moment_lower_bound_of_le]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/PhaseTypeDimensionBounds.lean#L28
[SSPRK.PhaseTypeData.variance_lower_bound_of_le]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/PhaseTypeDimensionBounds.lean#L15
[SSPRK.absoluteMonotonicityRadius]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/SSPRadius.lean#L29
[SSPRK.absolutelyMonotoneAt_absoluteMonotonicityRadius]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/Endpoint.lean#L179
[SSPRK.auxiliary_moment_class]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/MomentClassOperations.lean#L46
[SSPRK.eq_midpoint_of_sorted_transform]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/Proofs/SecondOrderClassification.lean#L17
[SSPRK.eq_sdirk_of_sorted_transform]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/Proofs/ThirdOrderClassification.lean#L34
[SSPRK.exists_variance_potential]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/VariancePotential.lean#L26
[SSPRK.lengthBias_independentSumLaw]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/LengthBiasConvolution.lean#L25
[SSPRK.lengthBias_normalized_variance]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/LengthBias.lean#L105
[SSPRK.lengthBias_probabilityMomentMixture]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/LengthBiasMixture.lean#L37
[SSPRK.length_biased_component_bound]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/MomentAlgebra.lean#L64
[SSPRK.midpoint_radius]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/MidpointAttainment.lean#L99
[SSPRK.phaseBlock_third_moment]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/PhaseTypeBlockMoments.lean#L107
[SSPRK.phase_mixture_chain_classification_of_pos]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/PhaseMixtureChain.lean#L96
[SSPRK.phase_second_moment_bound]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/PhaseMomentBound.lean#L15
[SSPRK.phase_variance_chain_classification]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/PhaseChainEquality.lean#L132
[SSPRK.phase_variance_pointwise_of_potential]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/PhaseVariance.lean#L39
[SSPRK.rkN_nonneg]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/RKSubstochastic.lean#L48
[SSPRK.rkOmega_N_cu_ones_eq]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/RKTransform.lean#L155
[SSPRK.rkOmega_N_ones_eq]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/RKTransform.lean#L105
[SSPRK.rkOmega_N_sq_ones_eq]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/RKTransform.lean#L144
[SSPRK.rkP_substochastic]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/RKSubstochastic.lean#L18
[SSPRK.sdirk_order_three_node]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/SDIRKOrder.lean#L217
[SSPRK.sdirk_order_three_tree]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/SDIRKOrder.lean#L288
[SSPRK.sdirk_radius]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/ThirdOrderOptimality.lean#L15
[SSPRK.second_order_bound_of_weighted_moment_inequality]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SecondOrderBound.lean#L22
[SSPRK.second_order_classification_at_bound]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/Proofs/SecondOrderClassification.lean#L69
[SSPRK.second_order_optimal_radius]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/SecondOrderOptimality.lean#L25
[SSPRK.second_order_radius_bound]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/Radius.lean#L21
[SSPRK.second_order_rk_ssp_bound]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SecondOrderBound.lean#L28
[SSPRK.second_order_unique_at_twice_stages]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SecondOrderEquality.lean#L18
[SSPRK.second_order_unique_of_radius_eq]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/SecondOrderRadiusEquality.lean#L15
[SSPRK.third_order_bound_of_quadratic]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/ThirdOrderBound.lean#L27
[SSPRK.third_order_classification_at_bound]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/Proofs/ThirdOrderClassification.lean#L93
[SSPRK.third_order_optimal_radius]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/ThirdOrderOptimality.lean#L37
[SSPRK.third_order_quadratic_of_moment_bound]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/ThirdOrderBound.lean#L19
[SSPRK.third_order_radius_bound]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/ThirdOrderRadius.lean#L7
[SSPRK.third_order_rk_ssp_bound]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/ThirdOrderBound.lean#L37
[SSPRK.third_order_unique_at_radius]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/ThirdOrderEquality.lean#L19
[SSPRK.third_order_unique_of_radius_eq]: https://github.com/quanfan-zi/ssp-rk-formalization/blob/a784414ad1cdb22ae9e868a8e829e80b9b035b23/lean/SSPRK/ThirdOrderRadiusEquality.lean#L15
