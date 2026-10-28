# V2.10 formalization notes

This is the working record for the manuscript supplied in
`SSP_Runge_Kutta_Sharp_Boundary.zip`. The source files in `docs/paper-v2.10/` were
extracted without editing. The branch is `codex/paper-v2-10-formalization`, based on
`origin/main`.
The remote has no `master`; using `main` was explicitly confirmed by the user.
The archive and its four extracted manuscript files are intentionally Git-ignored
at the user's request. The Lean build does not require the manuscript files.
The compiled [V2.10 PDF](V2.10.pdf) is tracked. It was built from the unchanged source with
pdfLaTeX and BibTeX; the final 22-page output has resolved references and citations.

## Entry inventory

The SIAM class shares one counter between definitions, propositions, theorems,
lemmas, and examples. Thus the first proposition is 2.3, and the acyclic theorem
is 4.4 because the state-elimination lemma is 4.3. All three propositions and all
five theorems have public entries. Numbers use underscores in module names.

| Paper | Public file in `lean/` | Main declaration in `SSPRK.Paper` |
| --- | --- | --- |
| Proposition 2.3 | `Proposition_2_3_TransientSubintensity.lean` | `proposition_2_3` |
| Proposition 3.1 | `Proposition_3_1_RKPHRepresentation.lean` | `proposition_3_1` |
| Proposition 3.2 | `Proposition_3_2_RKPHMoments.lean` | `proposition_3_2` |
| Theorem 4.1 | `Theorem_4_1_AldousShepp.lean` | `theorem_4_1` |
| Theorem 4.2 | `Theorem_4_2_ThirdMomentBound.lean` | `theorem_4_2` |
| Theorem 4.4 | `Theorem_4_4_AcyclicMomentRatio.lean` | `theorem_4_4` |
| Theorem 5.1 | `Theorem_5_1_SecondOrderOptimality.lean` | `theorem_5_1` |
| Theorem 5.2 | `Theorem_5_2_ThirdOrderOptimality.lean` | `theorem_5_2` |

`Main.lean` imports these entries and retains the existing internal formalization.
The four RK bound and equality modules are in `lean/SSPRK/Proofs/`. The root `lean/` directory contains `Main.lean` and
the eight numbered proposition/theorem files.
All eight statements and proofs have been checked. No `sorry` remains in the
project Lean sources. Successful elaboration alone would not establish this:
the completed strict axiom audit also checked all imported project declarations,
required all eight entries, and rejected `sorryAx`. The coverage and audit scripts
were subsequently removed at the user's request; the results below record the completed
verification. Run `lake build` from `lean/` to check the proofs.

## Statement interpretation

- Proposition 2.3 expresses transience by survival probabilities tending to zero
  from every state under some positive uniformizing clock. This premise contains
  no determinant assumption. Necessity uses finite geometric sums and determinant
  continuity; it does not read the transience field of `PhaseTypeData`.
  A companion conclusion constructs `PhaseTypeData` and the canonical CTMC for
  every initial subprobability row, with almost-sure finite absorption. Its measure
  is already identified with the canonical absorption law. This also handles the
  empty-state case. No uniqueness theorem identifying an arbitrary externally
  supplied CTMC with this uniformized construction is asserted.
- Proposition 3.1 uses the existing four absolute-monotonicity conditions,
  including invertibility. Its probability row is normalized explicitly.
  Proposition 3.2 keeps the factor $1/\sigma$ in every positive moment.
- Theorem 4.1 specifies a fixed transient start. Its equality conclusion describes
  the generator and the initial state of a sequential equal-rate chain, not merely
  equality of a few moments. The bound is stated without division by the squared
  mean; the mean is positive under the stated assumptions.
- Theorems 4.2 and 4.4 require initial transient mass one. Their equality conclusions
  concern the full Erlang law, without an additional zero atom. Theorem 4.4 covers
  each positive integer $k$, including $k=1$, and equality for each fixed $k$.
- Acyclicity means that a simultaneous relabelling makes the transient generator
  lower triangular. This is the characterization used at the start of the paper's proof.
- Theorem 5.1 and 5.2 package the complete optimal radius, attainment, all relevant
  classical algebraic order conditions, and uniqueness up to simultaneous permutation.
  As in the existing project, general nonlinear ODE convergence/SSP semantics are
  represented through the paper's algebraic tableau conditions.

## Proof reuse and differences

### Uniformization and the variance theorem

The existing PH construction, all integral moment formulas, canonical absorption
law, matrix transform, and sharp chain classification are reused. The construction
starts with an Erlang mixture and identifies it with CTMC absorption afterwards;
the manuscript introduces the CTMC first. Both refer to the same probability law.

For Theorem 4.1, the current proof uses finite Green-matrix energy and a potential
built from ordered mean lifetimes. The paper cites the Aldous--Shepp remaining-life
martingale argument. The energy and equality mechanism are retained, but the
continuous-time martingale and optional-stopping derivation is not reproduced.
Reusing the already checked finite argument avoids replacing a valid theorem just
to change its presentation; this substitution remains explicit.

The second-order RK bound now normalizes the PH initial row and proves the paper's
stronger intermediate estimate $1+1/s\leq\sigma(1+2/r)$, before applying $\sigma\leq1$.
`PaperSecondOrderBound.lean` reuses the existing integral moments and variance theorem
for this step.

### All-order RK moments

Proposition 3.2 extends the existing first-three-moment formulas. Its checked
proof follows the manuscript: cancel one Green factor in $wU=rb^T$, apply the
existing all-order PH integral formula, expand $(I+rA)^{j-1}$, and substitute the
chain order conditions. No branching conditions are inferred from chain conditions.

### Third-moment proof route

V2.10 uses a mixed-occupation expansion, an exact defect identity, and a
sum-of-squares remainder. `ThirdMomentDefect.lean` proves these scalar identities
and their equality conditions. `PhaseTypeThirdDefect.lean` connects them to a new
state-count induction; `PhaseTypeThirdDefectEquality.lean` uses vanishing squares
to recover variance equality. Theorem 4.2, the third-order RK bound, and the
third-order equality classifier now call this new route.

Existing Green block identities supply the same total-moment expansion. Using
these matrix identities instead of differentiating the joint occupation Laplace
transform is a representation-level substitution; it is not a formal proof of that
joint-transform differentiation. `MomentClass` retains both bounds to reuse scaling
and mixture interfaces; the smaller model's variance field is explicitly obtained
from the separate minimum-variance theorem. Mixture equality is first reduced to
the mass-corrected variance equality, rather than identifying every Erlang component
before comparing their rates.

### Acyclic moment ratios

The proof of Theorem 4.4 keeps
the paper's finite decreasing paths, complete homogeneous polynomials, normalized
Schur inequality, and mixture Cauchy--Schwarz step. The cited Schur inequality is
proved internally using finite weighted Cauchy--Schwarz and composition
counting. This fills in an external mathematical ingredient rather than assuming it.

The finite path-moment expansion is derived from the lower-triangular
generator/embedded-chain recurrence. Identifying these exact moments with the
existing absorption law avoids introducing a separate conditional-path probability
API. The connection is proved for every natural moment, including the zeroth;
path weights and moment identities are not assumptions of the public theorem.
Equality forces full-length paths and equal holding means. Since all full-length
paths share the top state's holding mean, the mixture has the sharp first two
moments. The existing variance-equality theorem then identifies its Erlang law,
instead of constructing a new conditional exponential-convolution law.

### Optimal tableaux

The two optimality entries reuse the existing supremum, attainment, order, and
uniqueness results. The SDIRK parameter $(s-1)/\sqrt{s^2-1}$ equals the manuscript's
$\sqrt{(s-1)/(s+1)}$ for $s\geq2$. `PaperOptimalityCoefficients.lean` proves this
identity and the equality of the two diagonal-coefficient expressions.
Existing uniqueness proofs recover a chain directly from moment equality. Any
further route changes will be recorded here when they are connected and checked.

## Verification record

Checked on 2026-10-28 with Lean 4.30.0 and the mathlib version pinned in
`lean/lake-manifest.json`:

- `lake build`: passed, 3,679 jobs, including every numbered entry and `Main`.
- Source-coverage check: all three
  propositions and five theorems found, with declarations, imports and libraries registered.
- Axiom audit: all 1,882 imported project declarations
  use only `propext`, `Classical.choice`, and `Quot.sound`. All eight numbered
  declarations and the four RK bound and equality theorem names were required by the audit.
- Proof-route audit: checked actual elaborated dependencies
  of the transience criterion, the Schur/path argument, the normalized second-order
  estimate, and the third-moment defect proof used by Theorems 4.2 and 5.2.

A separate subagent compared all eight entry statements with the manuscript's
quantifiers, normalization, equality cases and optimum definitions. Its concern
about the original 2.3 necessity direction led to the determinant-free survival
criterion described above. This is an internal source review, not an external
mathematician's endorsement.
