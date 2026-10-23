import CantorFubini.SourceIntegralOrder
import CantorFubini.ParameterMeasure
import Mathlib.MeasureTheory.Integral.Layercake

/-! The manuscript's ordinary-real integral agrees with ordinary integration
when the valuation actually comes from a finite Radon measure. No such
representation is asserted for arbitrary valuations. -/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u
namespace CantorFubini

theorem IsRealLSC.measurable {X : Type u} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {f : X → ℝ}
    (hf : IsRealLSC f) : Measurable f :=
  measurable_of_Ioi (fun a => (hf a).measurableSet)

theorem IsRealLSC.integrable_of_unit {X : Type u} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : IsRealLSC f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    Integrable f μ := by
  apply (integrable_const (1 : ℝ)).mono' hf.measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 x)] using hf1 x)

theorem sourceIntegral_radonValuation {X : Type u}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [Measure.InnerRegular μ]
    (f : X → ℝ) (hf : IsRealLSC f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    sourceIntegral (radonValuation μ) f = ∫ x, f x ∂μ := by
  have hfi := hf.integrable_of_unit μ hf0 hf1
  have hcut : (∫ a : ℝ in Ioi 0, μ.real {x | a < f x}) =
      ∫ a : ℝ in Ioc 0 1, μ.real {x | a < f x} := by
    apply setIntegral_eq_of_subset_of_ae_diff_eq_zero
      nullMeasurableSet_Ioi Ioc_subset_Ioi_self
    apply Filter.Eventually.of_forall
    intro a ha
    have ha1 : 1 < a := lt_of_not_ge (fun ha1 => ha.2 ⟨ha.1, ha1⟩)
    have he : {x | a < f x} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact not_lt_of_ge ((hf1 x).trans ha1.le)
    simp [measureReal_def, he]
  rw [sourceIntegral_eq_strictLevels _ _ hf, integral_Icc_eq_integral_Ioc]
  simpa only [radonValuation_apply, measureReal_def] using
    (hfi.integral_eq_integral_meas_lt (Filter.Eventually.of_forall hf0)).trans hcut |>.symm

end CantorFubini
