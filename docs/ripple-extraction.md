# Local CTMC extraction

The `codex/ripple-extraction` branch replaces the Ripple package with the subset
needed by the completed phase-type CTMC semantics. Its starting checkpoint is
`b879bcf07c4ad7d290e856298f9d5eced6092652` on `codex/third-order-proof`.

## Provenance and license

The source is [pcbcos/Ripple](https://github.com/pcbcos/Ripple) at commit
`83d6a77319d1bbb9bd397f9613244d396dc48583`. The extracted files derive from
`Ripple/CTMC/DTMC.lean`, `Ripple/CTMC/CTMC.lean`, and
`Ripple/CTMC/CanonicalLaw.lean`. Ripple is licensed under Apache-2.0; the complete
upstream license is retained in [Ripple-Apache-2.0.txt](../licenses/Ripple-Apache-2.0.txt).
No upstream NOTICE file was present at that revision.

The local file headers identify the source revision and modifications. Existing
declaration documentation and the upstream namespace `Ripple.CTMC` are retained
for compatibility. This namespace is a Lean name and does not require a Lake
package named Ripple.

## Extraction boundary

| Local module | Retained functionality |
| --- | --- |
| `SSPRK.CTMC.DTMC` | PMF transition rows and iterated transitions |
| `SSPRK.CTMC.Core` | Finite generators, exit rates, embedded jump chain, exponential holding law, total jump-hold kernel |
| `SSPRK.CTMC.CanonicalLaw` | Ionescu-Tulcea record measure, history-next law, deterministic initial marker, almost-sure holding and transition properties |

These three files contain 63 handwritten declarations and 898 lines in total,
including file headers, comments, and blank lines.

The extraction excludes Ripple's transition-semigroup results, stationary and
reversed chains, recurrence machinery, and general process/filtration framework.
The manuscript-specific PH constructions, moment bounds, equality classifications,
and absorption/occupation laws remain in the existing SSPRK modules.

The helper reading the last state of a finite history now refers directly to the
record coordinate. It therefore does not require Ripple's `CTMCPath` or
`recordTrajectoryToPath`. The continuous-time state readout remains the project's
`recordStateAt`, including its absorbing-state value after the last jump.

## Reproducible dependency audit

From `lean/`, after a successful build:

```sh
lake env lean scripts/AuditCTMC.lean
```

The JSON output distinguishes direct references from their transitive closure and
records the defining module and source lines of each constant. Roots are all
declarations defined in the imported project modules, identified by module
ownership. This includes `CanonicalStateMarginals.lean`, even though it uses the
`Ripple.CTMC.QMatrix` namespace. The local extraction modules are excluded from
the roots and treated as the audited boundary instead.

The audit examines elaborated types and proof/definition values, including opaque
values. Its counts include compiler-generated declarations; they are not counts
of handwritten theorems. Source imports and elaboration-only conveniences require
separate checks: a constant audit alone does not prove independence from a package.
The output also reports all imported `Ripple.*` modules and the union of axioms
used transitively by every project root.

The original graph contained 1,485 project declarations, 51 direct Ripple constants,
and 85 Ripple constants in the transitive closure. The saved
[original inventory](audits/ripple-before.json) includes all names and source ranges.
Its four imported upstream files have 5,883 lines in total, including comments.

One elaboration-only dependency surfaced during integration: the zero-step marginal
proof had used Ripple's `[simp]` lemma `DTMC.stepN_zero`. Its reflexive proof had
disappeared from the elaborated term, so it was absent from the constant inventory.
The local proof now explicitly unfolds `DTMC.stepN`; the unused convenience lemma
does not need to be retained.

The [final inventory](audits/ripple-after.json) reports 1,496 project declarations
(including generated proof helpers), 50 direct local CTMC constants, and 76 in
their transitive closure. The module breakdown is:

| Defining module | Constants in the final closure |
| --- | ---: |
| `SSPRK.CTMC.DTMC` | 6 |
| `SSPRK.CTMC.Core` | 46 |
| `SSPRK.CTMC.CanonicalLaw` | 24 |

Re-elaboration changes generated proof-helper counts, so the root counts before
and after are not counts of added mathematical statements. The existing SSPRK
source changes are three import substitutions and three proof simplifications.

## Validation

On 2026-09-11, the integrated `lake build` succeeded with 3,647 jobs after removing
the Ripple Lake requirement and lockfile entry. The affected local CTMC, path,
absorption, and occupation modules were rebuilt. The effective `LEAN_PATH`
contains mathlib and its dependencies, the project's own build directory, and
Lean's standard library; it contains no Ripple package directory.
The final audit independently reports an empty `externalRippleModules` array.
The union of transitive axioms over all 1,496 project roots is exactly `propext`,
`Classical.choice`, and `Quot.sound`.

Source scans find no external `import Ripple.*` in the project and no proof
placeholders, native decision shortcuts, or custom axiom declarations in the
integrated mathematical modules. The retained license is byte-for-byte identical
to upstream (SHA-256 `3ddf9be5c28fe27dad143a5dc76eea25222ad1dd68934a047064e56ed2fa40c5`).
The Lean version and mathlib revision are unchanged.

## Mathematical scope

The extraction changes dependency ownership, two history-coordinate proof
simplifications, and that zero-step unfolding. It preserves the existing SSPRK
theorem statements. The variance inequality still uses the finite Green/energy
proof; the manuscript's separate continuous-time martingale/optional-stopping
argument has not been formalized.
