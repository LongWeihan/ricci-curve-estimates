import CurveControl
import Lean

/-!
Read the curated blueprint and resolve its declarations in the actual imported
Lean environment. Export checked types and docstrings for the static reference
pages. This checks declaration correspondence, not the informal mathematics.
-/
open Lean Elab Command
set_option maxHeartbeats 10000000
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
set_option pp.proofs true

run_cmd do
  let source ← liftIO <| IO.FS.readFile "blueprint/blueprint.json"
  let document ← ofExcept <| Json.parse source
  let nodes ← ofExcept <| document.getObjValAs? (Array Json) "nodes"
  let mut names : Array Name := #[]
  for node in nodes do
    let mappings ← ofExcept <| node.getObjValAs? (Array Json) "lean"
    for mapping in mappings do
      let declarations ← ofExcept <| mapping.getObjValAs? (Array String) "declarations"
      for declaration in declarations do
        let name := declaration.toName
        unless names.contains name do names := names.push name
  if names.isEmpty then throwError "Blueprint contains no Lean declarations."
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut records := #[]
  for name in names do
    let info ← getConstInfo name
    let type ← liftTermElabM <| Meta.ppExpr info.type
    let printedType := type.pretty
    if printedType.contains '⋯' then
      throwError "Pretty printer elided part of the type of {name}."
    let documentation ← liftIO <| findDocString? env name
    let some moduleIdx := env.getModuleIdxFor? name
      | throwError "No defining module for {name}."
    let moduleName := env.header.moduleNames[moduleIdx.toNat]!
    let axs ← collectAxioms name
    unless (axs.filter fun ax => !allowed.contains ax).isEmpty do
      throwError "Extra reachable axioms in blueprint declaration {name}."
    let ranges ← findDeclarationRanges? name
    records := records.push <| Json.mkObj [
      ("declaration", toJson name.toString),
      ("module", toJson moduleName.toString),
      ("type", toJson printedType),
      ("docstring", toJson (documentation.getD "")),
      ("line", toJson (ranges.map fun r => r.range.pos.line)),
      ("axioms", toJson (axs.map Name.toString))]
  let output := Json.mkObj [
    ("checked_declarations", toJson names.size),
    ("extra_axioms", Json.arr #[]),
    ("records", Json.arr records)]
  liftIO <| IO.FS.createDirAll "verification"
  liftIO <| IO.FS.writeFile "verification/blueprint-declarations.json" (output.pretty ++ "\n")
  logInfo m!"Resolved {names.size} blueprint declarations and exported their Lean types."
