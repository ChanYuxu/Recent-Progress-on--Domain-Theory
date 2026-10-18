import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.ConeForestConstruction
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.StandardConeFacts

/-!
# Property D for algebraic Yoneda-complete spaces

The cone-forest theorem is instantiated here with the now-proved analytic
cone facts.
-/

set_option autoImplicit false

open Set Function Topology
open scoped NNReal ENNReal Topology

noncomputable section

universe u

namespace LipschitzYonedaFinalTopology
namespace QuasiMetric

variable {X : Type u} (d : QuasiMetric X)

/-- The complete algebraic case of the manuscript's main theorem. -/
theorem IsAlgebraic.propertyD
    (halgebraic : d.IsAlgebraic)
    (hcomplete : d.IsYonedaComplete) :
    d.PropertyD :=
  propertyD_of_standardConeFacts d halgebraic.isStandard
    (d.standardConeFacts halgebraic.isStandard)
    halgebraic.hasEnoughCenterPoints hcomplete

end QuasiMetric
end LipschitzYonedaFinalTopology
