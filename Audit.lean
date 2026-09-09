import CurveControl
import Lean

/-!
Enumerate declarations from the imported CurveControl modules using Lean's
environment, including generated declarations and named instances. Reject any
reachable axiom outside the standard classical foundation. This is mechanical
evidence; independent mathematical interpretation is recorded separately.
-/

open Lean Elab Command

set_option maxHeartbeats 10000000

run_cmd do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun names name _ => Id.run do
    if let some idx := env.getModuleIdxFor? name then
      if let some modName := env.header.moduleNames[idx.toNat]? then
        if (`CurveControl).isPrefixOf modName then
          return names.push name
    return names
  let names := names.qsort Name.lt
  if names.isEmpty then
    throwError "No CurveControl declarations found; check root imports."
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut records := #[]
  for name in names do
    let axs ← collectAxioms name
    let extras := axs.filter fun ax => !allowed.contains ax
    unless extras.isEmpty do
      throwError "Unexpected reachable axioms for {name}: {extras}"
    records := records.push <| Json.mkObj [
      ("declaration", toJson name.toString),
      ("axioms", toJson (axs.map Name.toString))]
  let output := Json.mkObj [
    ("checked_declarations", toJson names.size),
    ("modules", toJson ((env.header.moduleNames.filter fun n =>
      (`CurveControl).isPrefixOf n).map Name.toString)),
    ("allowed_axioms", toJson (allowed.map Name.toString)),
    ("extra_axioms", Json.arr #[]),
    ("records", Json.arr records)]
  liftIO <| IO.FS.createDirAll "verification"
  liftIO <| IO.FS.writeFile "verification/reachable-axioms.json" (output.pretty ++ "\n")
  logInfo m!"Checked {names.size} CurveControl declarations, including generated declarations; no extra axioms."
