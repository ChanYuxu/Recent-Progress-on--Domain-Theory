import FiniteValuationApproximable.ContinuousValuation.VOneRetract
import FiniteValuationApproximable.GlobalValuation

/-!
# Global transfer for normalized continuous valuations

This module closes source theorem `thm:global-Vone`.  The genuine
subprobability valuation space is FVA by the global valuation-transfer theorem,
and probability valuations form its continuous retract whenever the base FVA
domain has a least element.
-/

set_option autoImplicit false

universe u

namespace FiniteValuationApproximable

variable {D : Type u} [PartialOrder D]

/-- Source theorem `thm:global-Vone`: normalized continuous valuations over an
FVA domain are FVA, once the finite double-valuation generators required by the
global subprobability transfer are available. -/
theorem global_vOne_of_finite_double_generators
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u})
    (hD : IsFVA.{u, u} D) :
    IsFVA.{u, u} (ContinuousValuation.VOne D) := by
  apply IsFVA.retract
    (ContinuousValuation.vOneVSubContinuousSectionRetractionPair
      hD.hasLeastElement)
  exact global_vSub_of_finite_double_generators hFiniteDouble hD

end FiniteValuationApproximable
