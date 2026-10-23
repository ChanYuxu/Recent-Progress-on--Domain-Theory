import CantorFubini.ValuationIntegral
import CantorFubini.MeasureLayercake
import CantorFubini.ParameterMeasure

/-! Choquet integration for an actual Radon measure agrees with its Lebesgue
integral, including ENNReal-valued LSC functions that take infinite values. -/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u
namespace CantorFubini

theorem vIntegral_radonValuation {X : Type u} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [Measure.InnerRegular μ] [SFinite μ]
    (f : X → ℝ≥0∞) (hf : IsVLSC f) :
    vIntegral (radonValuation μ) f = ∫⁻ x, f x ∂μ := by
  have hfm : Measurable f := measurable_of_Ioi (fun a => (hf a).measurableSet)
  rw [vIntegral_eq_strictLevels _ hf]
  exact (lintegral_ennreal_layercake μ f hfm).symm

end CantorFubini
