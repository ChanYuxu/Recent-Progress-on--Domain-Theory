import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.CompletionRetract

/-!
# Main theorem: property D for continuous Yoneda-complete spaces

This is Theorem `thm:main` of
`lipschitz_yoneda_final_topology_paper_fifth_audit.tex`.
-/

set_option autoImplicit false

noncomputable section

universe u v

namespace LipschitzYonedaFinalTopology
namespace QuasiMetric

variable {X : Type u} (d : QuasiMetric X)

/-- **Main theorem.** Every continuous Yoneda-complete quasi-metric space
has property D. -/
theorem IsContinuous.propertyD
    (hcontinuous : d.IsContinuous)
    (hcomplete : d.IsYonedaComplete) :
    d.PropertyD := by
  let R : d.YonedaDScottRetract (Completion.quasiMetric d) :=
    Completion.yonedaDScottRetract d hcontinuous hcomplete
  apply R.propertyD
  exact (Completion.isAlgebraic d).propertyD
    (Completion.quasiMetric d) (Completion.isYonedaComplete d)

/-- Non-method form of the headline theorem for convenient downstream use.
-/
theorem continuous_yonedaComplete_propertyD
    (hcontinuous : d.IsContinuous)
    (hcomplete : d.IsYonedaComplete) :
    d.PropertyD :=
  hcontinuous.propertyD d hcomplete

/-- Source corollary `cor:functional`, stated for the cofinal integer layers
used by the Lean layer system. -/
theorem IsContinuous.continuous_iff_integerLayerwise
    (hcontinuous : d.IsContinuous)
    (hcomplete : d.IsYonedaComplete)
    (Z : Type v) [TopologicalSpace Z] (F : d.LInf → Z) :
    Continuous F ↔
      ∀ n : ℕ, Continuous (fun f : d.integerLayer n ↦ F f) :=
  (d.layerSystem.propertyD_iff_universal_continuity).1
    (hcontinuous.propertyD d hcomplete) Z F

end QuasiMetric
end LipschitzYonedaFinalTopology
