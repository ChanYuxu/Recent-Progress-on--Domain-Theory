import ChainApproximation
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

set_option maxRecDepth 10000
set_option maxHeartbeats 0

open Lean Elab Command in
elab "#audit_chain_approximation" : command => do
  let env ← getEnv
  let isLocal := fun n : Name ↦
    n.toString.startsWith "ChainApproximation." ||
      n.toString.startsWith "_private.ChainApproximation."
  let mut rows : Array Json := #[]
  for (n, ci) in env.constants.toList do
    if isLocal n then
      let axioms ← collectAxioms n
      let deps := ci.getUsedConstantsAsSet.toList.filter isLocal
      let kind := match ci with
        | .axiomInfo _ => "axiom"
        | .thmInfo _ => "theorem"
        | .defnInfo _ => "definition"
        | .opaqueInfo _ => "opaque"
        | _ => "generated"
      rows := rows.push (Json.mkObj [
        ("name", toJson n.toString),
        ("kind", toJson kind),
        ("local_dependencies", toJson (deps.map Name.toString)),
        ("axioms", toJson (axioms.toList.map Name.toString))])
  logInfo (Json.compress (Json.mkObj [("declarations", Json.arr rows)]))

#audit_chain_approximation
