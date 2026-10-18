import LipschitzYonedaFinalTopology
import Lean.Util.CollectAxioms

/-! Audit the preserved paper declarations after standalone packaging. -/

#check LipschitzYonedaFinalTopology.QuasiMetric.Completion.yonedaDScottRetract
#print axioms LipschitzYonedaFinalTopology.QuasiMetric.Completion.yonedaDScottRetract
#check LipschitzYonedaFinalTopology.QuasiMetric.IsContinuous.propertyD
#print axioms LipschitzYonedaFinalTopology.QuasiMetric.IsContinuous.propertyD
#check LipschitzYonedaFinalTopology.QuasiMetric.IsContinuous.continuous_iff_integerLayerwise
#print axioms LipschitzYonedaFinalTopology.QuasiMetric.IsContinuous.continuous_iff_integerLayerwise

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let owner := env.header.moduleNames[index.toNat]!
    if owner.toString.startsWith "Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology" then
      let axioms ← Lean.collectAxioms name
      let unexpected := axioms.filter (fun axiomName => !allowed.contains axiomName)
      unless unexpected.isEmpty do
        throwError "Unexpected axioms for {name}: {unexpected}"
      checked := checked + 1
  logInfo m!"STANDALONE_AUDIT_PASS: {checked} paper declarations checked"
