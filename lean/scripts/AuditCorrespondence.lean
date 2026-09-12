import Main
import Lean

/-!
# Elaborated project dependencies for the paper correspondence review

Run `lake env lean scripts/AuditCorrespondence.lean` after `lake build`.
The JSON contains direct dependencies from declaration types and from proof/definition
values separately. Project ownership is determined by module, including the four root
entry modules and project CTMC declarations in the Ripple namespace. Generated helpers
are retained so a dependency path cannot disappear merely because it crosses one.

This is evidence about elaborated constants, not an automatic certificate that a proof
has the same mathematical meaning or follows the same argument as a paper.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let owner := fun name => (env.getModuleIdxFor? name).map fun idx =>
    env.header.moduleNames[idx.toNat]!
  let project := fun name => match owner name with
    | some mod => (`SSPRK).isPrefixOf mod ||
      #[`SecondOrderBound, `ThirdOrderBound, `SecondOrderEquality,
        `ThirdOrderEquality].contains mod
    | none => false
  let roots := #[`SSPRK.second_order_rk_ssp_bound, `SSPRK.third_order_rk_ssp_bound,
    `SSPRK.second_order_unique_at_twice_stages, `SSPRK.third_order_unique_at_radius]
  let mut rootEntries : Array Json := #[]
  for name in roots do
    unless (env.find? name).isSome && project name do
      throwError "Missing entry theorem: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unexpected entry axiom: {ax}"
    rootEntries := rootEntries.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("axioms", toJson (axioms.map Name.toString))]
  let mut entries : Array Json := #[]
  for (name, ci) in env.constants.toList.mergeSort (fun a b => Name.lt a.1 b.1) do
    if project name then
      let typeDeps := ci.type.getUsedConstants.filter project |>.qsort Name.lt
      let valueDeps := (ci.value? (allowOpaque := true)).map
        (fun v => v.getUsedConstants.filter project |>.qsort Name.lt) |>.getD #[]
      let ranges ← findDeclarationRanges? name
      entries := entries.push <| Json.mkObj [
        ("name", toJson name.toString),
        ("module", toJson ((owner name).map Name.toString)),
        ("lines", toJson (ranges.map fun r => (r.range.pos.line, r.range.endPos.line))),
        ("kind", toJson (if ci matches .thmInfo _ then "theorem" else "other")),
        ("typeDependencies", toJson (typeDeps.map Name.toString)),
        ("valueDependencies", toJson (valueDeps.map Name.toString))]
  IO.println <| (Json.mkObj [
    ("roots", Json.arr rootEntries),
    ("declarations", Json.arr entries)]).compress
