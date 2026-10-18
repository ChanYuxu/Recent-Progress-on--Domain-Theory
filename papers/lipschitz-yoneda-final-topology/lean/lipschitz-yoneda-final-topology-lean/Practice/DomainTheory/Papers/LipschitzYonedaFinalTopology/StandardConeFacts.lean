import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.ConeApproximation
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.ConeContinuity

/-!
# Discharge of the standard cone facts

This module closes the last analytic interface used by the cone-forest
construction.  Every field of `StandardConeFacts` is now a theorem derived
from standardness and the source definitions.
-/

set_option autoImplicit false

open Set Function Topology
open scoped NNReal ENNReal Topology

noncomputable section

universe u

namespace LipschitzYonedaFinalTopology
namespace QuasiMetric

variable {X : Type u} (d : QuasiMetric X)

/-- The formerly abstract cone facts, constructed without additional
hypotheses. -/
def standardConeFacts
    (hstandard : d.IsStandard) : d.StandardConeFacts hstandard where
  sharp_of_inLayer α q hq :=
    hstandard.hasScottContinuousSharp d hq.1 hq.2
  finiteEnvelope_lower α center height hcenter :=
    d.finiteConeEnvelope_isLowerSemicontinuous
      α center height hcenter
  finiteEnvelope_yoneda α center height hcenter :=
    hstandard.finiteConeEnvelope_isYonedaContinuous
      d α center height hcenter

end QuasiMetric
end LipschitzYonedaFinalTopology
