# ssp-rk-formalization

Lean formalization of SSP-RK theory

This project is used for the Lean formal verification of the SSP-RK theory. Based on the main proof line of the paper V1.6, the repository mainly maintains Lean code.

## Current target

The current target is the second-order bound `r ≤ 2 * s`, stated as
`SSPRK.second_order_rk_ssp_bound` in [SecondOrder.lean](lean/SSPRK/SecondOrder.lean).

## Project structure

- `docs/V1.6.pdf`: reference manuscript.
- `lean/SSPRK/SecondOrder.lean`: theorem statement and future proof.
- `lean/Main.lean`: imports the modules checked by the default build.
- `lean/lean-toolchain` and `lean/lake-manifest.json`: pinned environment.
