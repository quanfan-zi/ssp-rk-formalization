import Main
import Lean

/-!
# Audit the CTMC extraction boundary

Run `lake env lean scripts/AuditCTMC.lean` from `lean/` after `lake build`.
Ownership is determined by module, not namespace: project declarations in the
`Ripple.CTMC` namespace are still roots. The audit follows constants in elaborated
types and proof/definition values, including opaque values, through the extracted
boundary. Mathlib and Lean cannot depend on this later boundary, so traversal
stops there. Generated declarations are included in the counts.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let owner := fun name => (env.getModuleIdxFor? name).map fun idx =>
    env.header.moduleNames[idx.toNat]!
  let boundary := fun name => match owner name with
    | some mod => (`Ripple).isPrefixOf mod || (`SSPRK.CTMC).isPrefixOf mod
    | none => false
  let project := fun name => match owner name with
    | some mod => (`SSPRK).isPrefixOf mod && !((`SSPRK.CTMC).isPrefixOf mod)
    | none => false
  let mut direct : NameSet := {}
  let mut axioms : NameSet := {}
  let mut roots := 0
  for (name, ci) in env.constants.toList do
    if project name then
      roots := roots + 1
      for ax in ← Lean.collectAxioms name do
        axioms := axioms.insert ax
      for dep in ci.getUsedConstantsAsSet do
        if boundary dep then direct := direct.insert dep
  let mut used := direct
  let mut pending := direct.toArray
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if let some ci := env.find? name then
      for dep in ci.getUsedConstantsAsSet do
        if boundary dep && !used.contains dep then
          used := used.insert dep
          pending := pending.push dep
  let mut entries : Array Json := #[]
  for name in used.toArray.qsort Name.lt do
    let ranges ← findDeclarationRanges? name
    entries := entries.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson ((owner name).map Name.toString)),
      ("direct", toJson (direct.contains name)),
      ("lines", toJson (ranges.map fun r => (r.range.pos.line, r.range.endPos.line)))]
  IO.println <| (Json.mkObj [
    ("projectDeclarations", toJson roots),
    ("projectAxioms", toJson (axioms.toArray.qsort Name.lt |>.map Name.toString)),
    ("externalRippleModules", toJson (env.header.moduleNames.filter
      ((`Ripple).isPrefixOf ·) |>.map Name.toString)),
    ("directConstants", toJson direct.size),
    ("transitiveConstants", toJson used.size),
    ("entries", Json.arr entries)]).compress
