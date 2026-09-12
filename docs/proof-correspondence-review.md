# Proof correspondence review record

## Reviewed snapshot

- Date: 2026-09-12.
- Mathematical source: `a784414ad1cdb22ae9e868a8e829e80b9b035b23` (`origin/main` after fetch).
- Review branch: `codex/proof-correspondence`, created from that exact revision.
- Manuscript: `docs/V1.6.pdf`, 23 pages; SHA-256
  `9ae32035fae9df6401a6759df4409804b1104a175f3f1fa99e478491e975a0c9`.
- Review method: Codex source reading, PDF text and rendered-page inspection,
  Lean compilation, and extraction of elaborated constant dependencies.
- Independent external mathematician review: **not performed**.
- Independent external Lean review: **not performed**.

This record accompanies [ProofCorrespondence.md](../ProofCorrespondence.md).
It does not represent a human referee's approval or a machine certificate of
equivalence between English mathematics and Lean.

## Checks actually performed

| Check | Inspected evidence | Result |
| --- | --- | --- |
| Four entry signatures | The four root `.lean` files; V1.6 (2.16), (2.26), (2.28), Theorems 5.2-5.3 and (5.1), (5.3)-(5.4) | Stage counts, matrix domains, invertibility, order conditions, positive parameter, coefficient formulas and simultaneous permutation agree with the stated subclaims |
| Full theorem packaging | `SSPRadius`, `Radius`, `ThirdOrderRadius`, both optimality modules, both radius-equality modules, and attainment declarations | Positive-parameter entries are supplemented by complete-radius bounds, canonical attainment, and endpoint-based uniqueness; three chain conditions are distinguished from full order three |
| Zero atom / initial weights | V1.6 (2.9), (2.21), (2.25)-(2.29); `RKPhaseType`, `PhaseTypeNormalization`, `PhaseTypeConditioning` | Code's unnormalized output law is distinguished from the positive conditional law; all three moment mass factors and both ratios were checked |
| B2 mechanism | `PhaseMomentBound`, `PhaseVariance`, potential construction; V1.6 pp. 10-11 and 18 | Same lifetime-energy mechanism, with a finite-matrix proof replacing the martingale/optional-stopping derivation |
| B3 mechanism | `PhaseTypeThirdMoment`, `PhaseTypeBlockMoments`, `PhaseTypeElimination`, `MomentAlgebra`, `MomentClassOperations`; V1.6 pp. 12-16 | Schur deletion, normalized block/return terms, zero-tail case, moment convolution, length-biased component inequalities and restoration of mixtures correspond; actual probability constructions are separate |
| E2/E3 mechanism | Both `Proofs/*Classification` modules, `PhaseMixtureChain`, `PhaseTypeThirdEquality`, `PhaseTypeThirdMixtureEquality`, `PhaseTypeThirdLaw`; V1.6 pp. 11, 16-17, 19-20 | Moment equality recovers the representation directly; law-level Erlang iff and independent Lemma 4.7 are not invoked by the entries |
| Actual use / non-use | `AuditCorrespondence.lean` plus `summarize_correspondence.py`; saved JSON contains type/value edges, positive paths, and negative results | The report's reachability table is based on elaborated terms, including generated and private project helpers, not import lists |
| Evidence and link consistency | Recomputed all 10 closures and 390 queries from the full graph; checked every saved witness edge, 59 declaration links against source ranges, and source/PDF SHA-256 hashes | All matched; every declaration in the four route tables is reachable from the indicated entry |
| Build / entry availability | `lake build` from `lean/` | Success, 3,653 jobs; all four entry modules are included in the default target |
| Trust basis | `lake env lean scripts/AuditProofs.lean` | All 1,620 imported project declarations use only `propext`, `Classical.choice`, `Quot.sound`; the script requires all four entry theorems |
| Community practice | Official Lean validation guide, leanblueprint README, Tao's PFR tour, ConNF project description | Linked readable proof explanations are established practice; declaration existence checks and green diagrams do not certify semantic or route fidelity |

The review inspected the full relevant manuscript text (pp. 4-20), including
the complete proof blocks on pp. 10-17; rendered pp. 15-16 and 18-20 were checked
against the extracted formulas. Claims about other manuscript sections are limited
to the definitions and supplementary facts explicitly discussed in the report.
No mathematical source, entry signature, or internal file organization was changed.
The environment was Lean 4.30.0 with mathlib pinned to
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

## External reviewer worksheet

These fields are intentionally unfilled. A reviewer should record what they
actually read and checked, with the snapshot or later commit used for review.

| Reviewer / expertise | Snapshot checked | Specific checks and objections | Decision / date |
| --- | --- | --- | --- |
| Mathematics reviewer: pending | Pending | Check the four statement translations; distinguish output/conditional laws; verify the Green-energy and block-moment explanations; assess each replacement | Pending |
| Lean reviewer: pending | Pending | Reproduce the build/axiom audit; inspect definitions and explicit entry assumptions; trace selected positive paths and confirm the negative-dependency claims | Pending |

Suggested questions for a substantive sign-off:

1. Do the order conditions, full SSP constraints, parameter ranges and radius
   definitions express the intended Theorems 5.2-5.3, at the algebraic-tableau level?
2. Are $\tau$, $\tau^\circ$, $\sigma$, and all normalization factors distinguished
   correctly, especially in third-order equality and the zero-tail induction case?
3. Does the potential/energy argument supply the paper's needed variance conclusion,
   and is replacing the continuous-time martingale argument acceptable for this review?
4. Do the Schur complement and normalized moment triples represent the same
   state-elimination comparison, without assuming independence of actual occupations?
5. Is direct moment-to-representation rigidity acceptable in place of the paper's
   Erlang-law-then-Lemma-4.7 route? If exact dependency fidelity is required, record
   that requirement as unmet instead of approving a stronger claim.
6. Which declarations and dependency paths were checked personally? List unresolved
   issues and the evidence that would resolve them, rather than writing only “checked”.
