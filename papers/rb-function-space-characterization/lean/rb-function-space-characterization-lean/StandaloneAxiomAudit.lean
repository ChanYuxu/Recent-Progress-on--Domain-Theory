import RBFunctionSpaceCharacterization
import Lean.Util.CollectAxioms

/-! Audit the preserved paper declarations after standalone packaging. -/

#check RBFunctionSpace.universalTarget
#print axioms RBFunctionSpace.universalTarget
#check RBFunctionSpace.rb_implies_continuous_functionSpace
#print axioms RBFunctionSpace.rb_implies_continuous_functionSpace
#check RBFunctionSpace.rbCharacterization
#print axioms RBFunctionSpace.rbCharacterization
#check RBFunctionSpace.singleTargetCharacterization
#print axioms RBFunctionSpace.singleTargetCharacterization
#check RBFunctionSpace.finiteCoverExtraction
#print axioms RBFunctionSpace.finiteCoverExtraction
#check RBFunctionSpace.AX.functionSpaceRetract
#print axioms RBFunctionSpace.AX.functionSpaceRetract

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound, `RBFunctionSpace.rb_functionSpace_continuous, `RBFunctionSpace.continuous_functionSpace_compact_or_pointedComponents]
  let mut checked := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let owner := env.header.moduleNames[index.toNat]!
    if owner.toString.startsWith "Practice.DomainTheory.Papers.RBFunctionSpace" then
      let axioms ← Lean.collectAxioms name
      let unexpected := axioms.filter (fun axiomName => !allowed.contains axiomName)
      unless unexpected.isEmpty do
        throwError "Unexpected axioms for {name}: {unexpected}"
      checked := checked + 1
  logInfo m!"STANDALONE_AUDIT_PASS: {checked} paper declarations checked"
