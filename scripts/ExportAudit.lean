import InfiniteZero
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Export the actual constants and transitive axioms recorded by Lean.
This file is executed by `python3 scripts/update_status.py` after `lake build`.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let target ← getConstInfo ``InfiniteZero.thm_main
  unless target.type.isConstOf ``InfiniteZero.ConstructedPotentialMainTheorem do
    throwError "thm_main must retain its unconditional constructed-potential statement"
  if target.getUsedConstantsAsSet.contains ``sorryAx then
    throwError "thm_main must have an actual proof, not a direct admission"
  for (name, info) in env.constants.toList do
    let fromProjectModule := match env.getModuleIdxFor? name with
      | some idx =>
        let moduleName := env.header.moduleNames[idx]!
        moduleName == `InfiniteZero || "InfiniteZero.".isPrefixOf moduleName.toString
      | none => false
    if fromProjectModule || "InfiniteZero.".isPrefixOf name.toString ||
        "_private.InfiniteZero.".isPrefixOf name.toString then
      let kind := match info with
        | .thmInfo _ => "theorem"
        | .axiomInfo _ => "axiom"
        | .defnInfo _ => "definition"
        | .opaqueInfo _ => "opaque"
        | .inductInfo _ => "inductive"
        | _ => "generated"
      let axioms ← collectAxioms name
      let namesToJson := fun (ns : Array Name) =>
        Json.arr (ns.map (fun n => toJson n.toString))
      let row := Json.mkObj [
        ("name", toJson name.toString),
        ("kind", toJson kind),
        ("dependencies", namesToJson info.getUsedConstantsAsSet.toArray),
        ("axioms", namesToJson axioms)]
      liftM <| IO.println ("AUDIT_JSON " ++ row.compress)
