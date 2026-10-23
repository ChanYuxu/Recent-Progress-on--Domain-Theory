import ZFCFubini.PaperIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Source strict-level computations, entirely in ordinary real integration. -/

set_option autoImplicit false
open Set TopologicalSpace MeasureTheory
universe u
namespace ZFCFubini

theorem real_integral_unit_cutoff (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ a : ℝ in Icc (0 : ℝ) 1, if a < q then (1 : ℝ) else 0) = q := by
  classical
  have he : (fun a : ℝ => if a < q then (1 : ℝ) else 0) =
      (Iio q).indicator (fun _ => (1 : ℝ)) := by
    funext a
    by_cases ha : a < q <;> simp [ha, Set.indicator]
  rw [he]
  have hI := integral_indicator_const (μ := volume.restrict (Icc (0 : ℝ) 1))
    (1 : ℝ) (s := Iio q) measurableSet_Iio
  rw [hI]
  simp only [smul_eq_mul, mul_one]
  change ((volume.restrict (Icc (0 : ℝ) 1)) (Iio q)).toReal = q
  rw [Measure.restrict_apply measurableSet_Iio]
  have hi : Iio q ∩ Icc (0 : ℝ) 1 = Ico (0 : ℝ) q := by
    ext a
    constructor
    · rintro ⟨haq, ha0, _⟩
      exact ⟨ha0, haq⟩
    · rintro ⟨ha0, haq⟩
      exact ⟨haq, ha0, haq.le.trans hq1⟩
  rw [hi, Real.volume_Ico, sub_zero, ENNReal.toReal_ofReal hq0]

theorem real_integral_constant_cutoff (m q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ a : ℝ in Icc (0 : ℝ) 1, if a < q then m else 0) = m * q := by
  have he : (fun a : ℝ => if a < q then m else 0) =
      (fun a : ℝ => m * (if a < q then (1 : ℝ) else 0)) := by
    funext a
    by_cases ha : a < q <;> simp [ha]
  rw [he, integral_const_mul, real_integral_unit_cutoff q hq0 hq1]

theorem paperIntegral_eq_of_unit_superlevels
    {X : Type u} [TopologicalSpace X]
    (μ : ProbabilityValuation X) (f : X → ℝ) (hf : IsRealLSC f)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hprofile : ∀ a : ℝ, 0 ≤ a →
      realMass μ ⟨{x | a < f x}, hf a⟩ = if a < q then 1 else 0) :
    paperIntegral μ f = q := by
  rw [paperIntegral_eq_strictLevels μ f hf]
  calc
    (∫ a : ℝ in Icc (0 : ℝ) 1, realMass μ ⟨{x | a < f x}, hf a⟩) =
        ∫ a : ℝ in Icc (0 : ℝ) 1, if a < q then (1 : ℝ) else 0 :=
      setIntegral_congr_fun measurableSet_Icc (fun a ha => hprofile a ha.1)
    _ = q := real_integral_unit_cutoff q hq0 hq1

noncomputable def realIndicator {X : Type u} [TopologicalSpace X]
    (U : Opens X) (x : X) : ℝ := by
  classical
  exact if x ∈ U then 1 else 0

theorem realIndicator_isRealLSC {X : Type u} [TopologicalSpace X]
    (U : Opens X) : IsRealLSC (realIndicator U) := by
  classical
  intro a
  by_cases hn : a < 0
  · have he : {x | a < realIndicator U x} = univ := by
      ext x
      by_cases hx : x ∈ U <;> simp [realIndicator, hx, hn, show a < 1 by linarith]
    rw [he]
    exact isOpen_univ
  · by_cases h1 : a < 1
    · have he : {x | a < realIndicator U x} = (U : Set X) := by
        ext x
        by_cases hx : x ∈ U <;> simp [realIndicator, hx, hn, h1]
      rw [he]
      exact U.isOpen
    · have he : {x | a < realIndicator U x} = ∅ := by
        ext x
        by_cases hx : x ∈ U <;> simp [realIndicator, hx, hn, h1]
      rw [he]
      exact isOpen_empty

/-- Source preliminaries and the two inner integrals: characteristic functions
of actual opens integrate to the valuation's real mass. -/
theorem paperIntegral_realIndicator {X : Type u} [TopologicalSpace X]
    (μ : ProbabilityValuation X) (U : Opens X) :
    paperIntegral μ (realIndicator U) = realMass μ U := by
  classical
  rw [paperIntegral_eq_strictLevels μ _ (realIndicator_isRealLSC U)]
  have hcut (a : ℝ) (ha : 0 ≤ a) :
      realMass μ ⟨{x | a < realIndicator U x}, realIndicator_isRealLSC U a⟩ =
        if a < 1 then realMass μ U else 0 := by
    by_cases h1 : a < 1
    · have he : (⟨{x | a < realIndicator U x}, realIndicator_isRealLSC U a⟩ : Opens X) = U := by
        ext x
        by_cases hx : x ∈ U <;> simp [realIndicator, hx, h1, not_lt.mpr ha]
      rw [he, if_pos h1]
    · have he : (⟨{x | a < realIndicator U x}, realIndicator_isRealLSC U a⟩ : Opens X) = ⊥ := by
        ext x
        by_cases hx : x ∈ U <;> simp [realIndicator, hx, h1, not_lt.mpr ha]
      rw [he, realMass_empty, if_neg h1]
  calc
    (∫ a : ℝ in Icc (0 : ℝ) 1, realMass μ
        ⟨{x | a < realIndicator U x}, realIndicator_isRealLSC U a⟩) =
        ∫ a : ℝ in Icc (0 : ℝ) 1, if a < 1 then realMass μ U else 0 :=
      setIntegral_congr_fun measurableSet_Icc (fun a ha => hcut a ha.1)
    _ = realMass μ U := by
      simpa using real_integral_constant_cutoff (realMass μ U) 1 (by norm_num) le_rfl

end ZFCFubini
