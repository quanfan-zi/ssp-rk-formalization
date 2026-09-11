# Local CTMC code provenance

The project uses locally maintained CTMC code derived from Ripple. Ripple is not
a Lake package dependency. This document records source attribution and licensing.

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

## Local modules

| Local module | Retained functionality |
| --- | --- |
| `SSPRK.CTMC.DTMC` | PMF transition rows and iterated transitions |
| `SSPRK.CTMC.Core` | Finite generators, exit rates, embedded jump chain and holding laws |
| `SSPRK.CTMC.CanonicalLaw` | Canonical record measure and holding/transition properties |

The PH constructions, moment bounds, equality classifications, and absorption and
occupation laws are developed in the project modules that use this local foundation.

Current proof dependencies are checked with `lake env lean scripts/AuditProofs.lean`
from `lean/` after a successful build. The script audits all imported project
declarations, including the local CTMC modules, and checks the four core entries.
Historical extraction snapshots are no longer part of the maintained audit.
