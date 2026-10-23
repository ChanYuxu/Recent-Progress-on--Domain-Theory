import Mathlib.MeasureTheory.Integral.Layercake

/-! A real-threshold layer-cake formula for ENNReal-valued measurable
functions, including infinite values. This is only a theorem about an actual
measure; it does not extend an arbitrary valuation to a measure. -/

set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal
universe u
namespace CantorFubini

theorem lintegral_real_threshold (c : ℝ≥0∞) :
    (∫⁻ t : ℝ in Ioi 0, if ENNReal.ofReal t < c then (1 : ℝ≥0∞) else 0) = c := by
  classical
  by_cases hc : c = ∞
  · subst c
    simp [ENNReal.ofReal_lt_top, Real.volume_Ioi]
  · have hs : MeasurableSet {t : ℝ | ENNReal.ofReal t < c} :=
      measurableSet_lt ENNReal.measurable_ofReal measurable_const
    have he : {t : ℝ | ENNReal.ofReal t < c} ∩ Ioi 0 = Ioo 0 c.toReal := by
      ext t
      constructor
      · rintro ⟨ht, ht0⟩
        exact ⟨ht0, (ENNReal.ofReal_lt_iff_lt_toReal ht0.le hc).mp ht⟩
      · rintro ⟨ht0, ht⟩
        exact ⟨(ENNReal.ofReal_lt_iff_lt_toReal ht0.le hc).mpr ht, ht0⟩
    calc
      (∫⁻ t : ℝ in Ioi 0, if ENNReal.ofReal t < c then (1 : ℝ≥0∞) else 0) =
          (volume.restrict (Ioi (0 : ℝ))) {t : ℝ | ENNReal.ofReal t < c} := by
        simpa only [Set.indicator, Set.mem_setOf_eq, one_mul] using
          lintegral_indicator_const (μ := volume.restrict (Ioi (0 : ℝ)))
            hs (1 : ℝ≥0∞)
      _ = volume (Ioo 0 c.toReal) := by rw [Measure.restrict_apply hs, he]
      _ = c := by rw [Real.volume_Ioo, sub_zero, ENNReal.ofReal_toReal hc]

theorem lintegral_ennreal_layercake {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (f : X → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂μ) = ∫⁻ t : ℝ in Ioi 0, μ {x | ENNReal.ofReal t < f x} := by
  classical
  let F : ℝ → X → ℝ≥0∞ := fun t x =>
    if ENNReal.ofReal t < f x then 1 else 0
  have hF : Measurable (Function.uncurry F) := by
    exact Measurable.ite
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        (hf.comp measurable_snd)) measurable_const measurable_const
  have ht (t : ℝ) : (∫⁻ x, F t x ∂μ) = μ {x | ENNReal.ofReal t < f x} := by
    have hs : MeasurableSet {x | ENNReal.ofReal t < f x} :=
      measurableSet_lt measurable_const hf
    simpa only [F, Set.indicator, Set.mem_setOf_eq, one_mul] using
      lintegral_indicator_const (μ := μ) hs (1 : ℝ≥0∞)
  calc
    (∫⁻ x, f x ∂μ) = ∫⁻ x, (∫⁻ t : ℝ in Ioi 0, F t x) ∂μ := by
      apply lintegral_congr
      intro x
      exact (lintegral_real_threshold (f x)).symm
    _ = ∫⁻ t : ℝ in Ioi 0, (∫⁻ x, F t x ∂μ) :=
      (lintegral_lintegral_swap hF.aemeasurable).symm
    _ = ∫⁻ t : ℝ in Ioi 0, μ {x | ENNReal.ofReal t < f x} := by
      simp_rw [ht]

end CantorFubini
