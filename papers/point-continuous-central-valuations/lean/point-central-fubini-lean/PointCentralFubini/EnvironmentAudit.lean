import PointCentralFubini
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    let s := name.toString
    if s.startsWith "PointCentralFubini." ||
        (s.startsWith "_private.PointCentralFubini." && !(s.contains '✝')) then
      let kind := match ci with
        | .axiomInfo _ => "axiom"
        | .thmInfo _ => "theorem"
        | .defnInfo _ => "definition"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
        | .opaqueInfo _ => "opaque"
        | .quotInfo _ => "quotient"
      let ax ← collectAxioms name
      let typ ← liftTermElabM do
        return (← PrettyPrinter.ppExpr ci.type).pretty
      let json := Json.mkObj [
        ("name", toJson s),
        ("kind", toJson kind),
        ("type", toJson typ),
        ("directDependencies", toJson (ci.getUsedConstantsAsSet.toList.map Name.toString)),
        ("axioms", toJson (ax.toList.map Name.toString))]
      liftIO <| IO.println json.compress
