import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology

/-!
# Kernel-assumption audit

Running this file prints the assumptions of representative proved results.
The expected output contains only Lean/mathlib foundations such as
`propext`, `Classical.choice`, and `Quot.sound`; it must contain no
project-specific axiom.
-/

open LipschitzYonedaFinalTopology

#print axioms LayerSystem.propertyD_iff_isQuotientMap
#print axioms LayerSystem.propertyD_iff_universal_continuity
#print axioms LayerSystem.propertyD_of_retraction
#print axioms QuasiMetric.layerwiseOpen_isUpper
#print axioms QuasiMetric.finiteConeMax_eq_on_centers
#print axioms QuasiMetric.finiteConeInterpolation
#print axioms QuasiMetric.exists_uniform_root_margin
#print axioms QuasiMetric.FiniteConeForestData.branch_radius_tendsto_zero
#print axioms QuasiMetric.FiniteConeForestData.isOpen_pathHeight_sublevel
#print axioms QuasiMetric.FiniteConeForestData.isCompact_compactSaturation
#print axioms QuasiMetric.FunctionSpaceRetract.propertyD
#print axioms QuasiMetric.yonedaCompleteness_not_necessary_for_propertyD
#print axioms CompletionFormula.isOpen_strictSuperlevel_correctedSupremum
#print axioms FiniteLevelForest.pathSpace_isCompact
#print axioms FiniteLevelForest.isOpen_singleton_of_terminal
#print axioms LayerSystem.propertyD_iff_continuous_extension
#print axioms QuasiMetric.Completion.yonedaDScottRetract
#print axioms QuasiMetric.IsContinuous.propertyD
#print axioms QuasiMetric.continuous_yonedaComplete_propertyD
#print axioms QuasiMetric.IsContinuous.continuous_iff_integerLayerwise
