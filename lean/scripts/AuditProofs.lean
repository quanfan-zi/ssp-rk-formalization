import Main
import Lean

/-!
# Audit project proof dependencies

Run `lake env lean scripts/AuditProofs.lean` from `lean/` after `lake build`.
The audit checks every declaration owned by an imported project module, including
local CTMC modules and generated helpers. It follows transitive axiom dependencies
and requires the four core entry theorems to be present. Only the three standard
axioms listed below are accepted; an unfinished proof or an additional axiom fails.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let project := fun name => match env.getModuleIdxFor? name with
    | some idx =>
      let mod := env.header.moduleNames[idx.toNat]!
      (`SSPRK).isPrefixOf mod ||
        #[`SecondOrderBound, `ThirdOrderBound, `SecondOrderEquality,
          `ThirdOrderEquality].contains mod
    | none => false
  let entryTheorems := #[`SSPRK.second_order_rk_ssp_bound,
    `SSPRK.third_order_rk_ssp_bound, `SSPRK.second_order_unique_at_twice_stages,
    `SSPRK.third_order_unique_at_radius]
  for name in entryTheorems do
    unless (env.find? name).isSome && project name do
      throwError "Core entry theorem is missing from the audit: {name}"
  let mut axioms : NameSet := {}
  let mut declarations := 0
  for (name, _) in env.constants.toList do
    if project name then
      declarations := declarations + 1
      for ax in ← Lean.collectAxioms name do
        axioms := axioms.insert ax
  for ax in axioms.toArray do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "Unexpected project axiom: {ax}"
  IO.println <| (Json.mkObj [
    ("projectDeclarations", toJson declarations),
    ("coreEntryTheorems", toJson (entryTheorems.map Name.toString)),
    ("projectAxioms", toJson (axioms.toArray.qsort Name.lt |>.map Name.toString))]).compress
